// Package cfa implements cross-function analysis. The analyzer
// defined in this package looks at every function in the transitive
// dependencies of the program being analyzed and creates an abstraction
// for each one that can later be used to determine if a given call is safe.
package cfa

import (
	"fmt"
	"go/types"
	"reflect"
	"strconv"
	"strings"

	"github.com/google/go-flow-levee/internal/pkg/utils"

	"github.com/google/go-flow-levee/internal/pkg/config"
	"golang.org/x/tools/go/analysis"
	"golang.org/x/tools/go/analysis/passes/buildssa"
	"golang.org/x/tools/go/ssa"
)

// ResultType is a mapping from types.Object to cfa.Function
type ResultType = Functions

type Functions map[types.Object]Function

// A Function is an abstraction for a Go function.
// It can be queried about what it does with its arguments.
type Function interface {
	fmt.Stringer

	// TODO: consider "ReachesSink" name
	// Does this function sink its nth argument?
	Sinks(arg int) bool

	// If this argument is tainted, which return values are tainted?
	Taints(arg int) []int
}

type sink struct{}

func (s sink) Sinks(arg int) bool {
	return true
}

func (s sink) Taints(arg int) (tainted []int) {
	return
}

func (s sink) String() string {
	return "sink"
}

type sanitizer struct{}

func (s sanitizer) Sinks(arg int) bool {
	return false
}

func (s sanitizer) Taints(arg int) (tainted []int) {
	return
}

func (s sanitizer) String() string {
	return "sanitizer"
}

type genericFunc struct {
	sinks   []bool
	taints  [][]int
	params  int
	retvals int
}

func newGenericFunc(f *ssa.Function) genericFunc {
	params := f.Signature.Params().Len()
	return genericFunc{
		sinks:  make([]bool, params),
		taints: make([][]int, params),
		params: params,
	}
}

func (g genericFunc) Sinks(arg int) bool {
	// TODO: error if out of bounds?
	return arg < len(g.sinks) && g.sinks[arg]
}

func (g genericFunc) Taints(arg int) (tainted []int) {
	// TODO: error if out of bounds?
	if arg >= len(g.sinks) {
		return nil
	}
	return g.taints[arg]
}

func (g genericFunc) String() string {
	var b strings.Builder
	b.WriteString("genericFunc{ sinks: [")
	for i, reachesSink := range g.sinks {
		if reachesSink {
			b.WriteString(strconv.Itoa(i))
			if i < len(g.sinks)-2 {
				b.WriteByte(' ')
			}
		}
	}
	b.WriteString("], taints: ")
	b.WriteString(fmt.Sprintf("%v", g.taints))
	b.WriteString(" }")
	return b.String()
}

func (g genericFunc) Params() int {
	return g.params
}

func (g genericFunc) Retvals() int {
	return g.retvals
}

type funcFact struct {
	Function
}

func (f funcFact) AFact() {}

var Analyzer = &analysis.Analyzer{
	Name:       "cfa",
	Doc:        `This analyzer performs cross-function analysis in order to determine the behavior of every function in the transitive dependencies of the program being analyzed.`,
	Flags:      config.FlagSet,
	Run:        run,
	Requires:   []*analysis.Analyzer{buildssa.Analyzer},
	ResultType: reflect.TypeOf(new(ResultType)).Elem(),
	FactTypes:  []analysis.Fact{new(funcFact)},
}

var pkgDenylist = []string{
	"atomic",
	"race",
	"math",
	"bytealg",
	"internal",
	"sync",
	"runtime",
	"unsafe",
	"cpu",
	"sys",
	"reflect",
	"reflectlite",
	"io",
	"errors",
}

func run(pass *analysis.Pass) (interface{}, error) {
	for _, d := range pkgDenylist {
		pkgName := pass.Pkg.Name()
		if strings.HasPrefix(pkgName, d) {
			return Functions(nil), nil
		}
	}

	ssaInput := pass.ResultOf[buildssa.Analyzer].(*buildssa.SSA)

	conf, err := config.ReadConfig()
	if err != nil {
		return nil, err
	}

	for _, fn := range ssaInput.SrcFuncs {
		analyze(pass, conf, fn)
	}

	functions := map[types.Object]Function{}
	for _, f := range pass.AllObjectFacts() {
		// a panic here can only happen due to an internal error
		ff := f.Fact.(*funcFact)
		functions[f.Object] = ff.Function
	}
	return Functions(functions), nil
}

// this will be called at most twice for a given function
// it will get called exactly twice if the function is "discovered" during the analysis of a function
// that occurs before it in ssaInput.SrcFuncs
func analyze(pass *analysis.Pass, conf *config.Config, fn *ssa.Function) {
	// TODO: handle methods
	if fn.Signature.Recv() != nil {
		return
	}
	switch {
	case conf.IsSinkFunction(fn):
		pass.ExportObjectFact(fn.Object(), &funcFact{sink{}})

	case conf.IsSanitizerFunction(fn):
		pass.ExportObjectFact(fn.Object(), &funcFact{sanitizer{}})

	default:
		gf := analyzeGenericFunc(pass, conf, fn)
		pass.ExportObjectFact(fn.Object(), &funcFact{gf})
	}
}

func analyzeGenericFunc(p *analysis.Pass, c *config.Config, f *ssa.Function) genericFunc {
	gf := newGenericFunc(f)

	retVals, count := findRetvals(f)
	gf.retvals = count

	for i, param := range f.Params {
		reachesSink, taints := visit(p, c, retVals, param)
		// TODO: handle methods
		if len(gf.sinks) <= i {
			continue
		}
		gf.sinks[i] = reachesSink
		gf.taints[i] = taints
	}

	return gf
}

type visitor struct {
	pass        *analysis.Pass
	conf        *config.Config
	retVals     map[ssa.Value]int
	visited     map[ssa.Node]bool
	reachesSink bool
	taints      []int
}

func visit(p *analysis.Pass, conf *config.Config, retVals map[ssa.Value]int, param *ssa.Parameter) (reachesSink bool, taints []int) {
	v := visitor{
		pass:    p,
		conf:    conf,
		retVals: retVals,
		visited: map[ssa.Node]bool{},
	}

	v.dfs(param)

	return v.reachesSink, v.taints
}

func (v *visitor) dfs(n ssa.Node) {
	if v.visited[n] {
		return
	}
	v.visited[n] = true

	// might not need this at all? return instructions are a thing? as in they return values?
	// note to self: visualize ssa graph more often
	if val, ok := n.(ssa.Value); ok {
		if i, isRet := v.retVals[val]; isRet {
			v.taints = append(v.taints, i)
		}
	}

	if _, ok := n.(*ssa.Return); ok {
		return
	}

	if call, ok := n.(*ssa.Call); ok {
		if call.Call.IsInvoke() {
			return
		}
		f, _ := call.Call.Value.(*ssa.Function)
		fact := &funcFact{}
		hasFact := v.pass.ImportObjectFact(f.Object(), fact)
		if !hasFact {
			analyze(v.pass, v.conf, f)
		}
		hasFactNow := v.pass.ImportObjectFact(f.Object(), fact)
		if !hasFactNow {
			panic("ʕノ◔ϖ◔ʔノ彡┻━┻")
		}

		switch ff := fact.Function.(type) {
		case sink:
			v.reachesSink = true
			// value has reached a sink, stop traversing
			return
		case sanitizer:
			// value has been sanitized, stop traversing
			return
		case genericFunc:
			// if func has multiple retvals, will have an extract
			// otherwise func itself is a value so dfsing through it = dfsing through its retval,
			// just don't dfs through its arguments
			switch ff.Retvals() {
			case 0:
				// TODO: validate this
				// function has no return value, so nowhere to traverse to
				return

			case 1:
				for i, a := range call.Call.Args {
					if v.visited[a.(ssa.Node)] {
						v.reachesSink = v.reachesSink && ff.Sinks(i)
						argTaints := ff.Taints(i)
						if len(argTaints) == 0 {
							// this arg does not taint the return values
							continue
						}
						// since this function has only 1 return value, we know it is tainted
						break
						// break so we'll hit the operands/referrers instructions later
					}
				}

			// >=2 retvals
			default:
				extractMap := map[int]*ssa.Extract{}
				for _, r := range *call.Referrers() {
					if e, ok := r.(*ssa.Extract); ok {
						extractMap[e.Index] = e
					}
				}
				extracts := make([]*ssa.Extract, len(extractMap))
				for i, e := range extractMap {
					extracts[i] = e
				}
				taintUnion := map[int]bool{}
				for i, a := range call.Call.Args {
					if v.visited[a.(ssa.Node)] {
						v.reachesSink = v.reachesSink || ff.Sinks(i)
						for _, j := range ff.Taints(i) {
							taintUnion[j] = true
						}
					}
				}
				// function has >= 2 return values, but they are "swallowed"
				if len(extracts) == 0 {
					return
				}
				for i := range taintUnion {
					v.dfs(extracts[i])
				}
				return
			}
		}
	}

	referrers := n.Referrers()
	if referrers != nil {
		for _, r := range *referrers {
			n := r.(ssa.Node)
			v.dfs(n)
		}
	}

	var operands []*ssa.Value
	operands = n.Operands(operands)
	if operands != nil {
		for _, o := range operands {
			n, ok := (*o).(ssa.Node)
			if !ok {
				continue
			}
			if al, isAlloc := (*o).(*ssa.Alloc); isAlloc {
				if _, isArray := utils.Dereference(al.Type()).(*types.Array); !isArray {
					return
				}
			}
			v.dfs(n)
		}
	}
}

func findRetvals(f *ssa.Function) (valToPos map[ssa.Value]int, count int) {
	retvals := map[ssa.Value]int{}
	for _, b := range f.Blocks {
		if len(b.Instrs) == 0 {
			continue
		}
		last := b.Instrs[len(b.Instrs)-1]
		ret, ok := last.(*ssa.Return)
		if !ok {
			continue
		}
		for i, res := range ret.Results {
			retvals[res] = i
		}
		count = len(ret.Results)
	}
	return retvals, count
}
