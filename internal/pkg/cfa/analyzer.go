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

	// If these arguments are tainted, which return values are tainted?
	Taints(args ...int) []int
}

type sink struct{}

func (s sink) Sinks(arg int) bool {
	return true
}

func (s sink) Taints(args ...int) (tainted []int) {
	return
}

func (s sink) String() string {
	return "sink"
}

type sanitizer struct{}

func (s sanitizer) Sinks(arg int) bool {
	return false
}

func (s sanitizer) Taints(args ...int) (tainted []int) {
	return
}

func (s sanitizer) String() string {
	return "sanitizer"
}

type genericFunc struct {
	sinks  []bool
	taints map[int][]int
}

func newGenericFunc(f *ssa.Function) genericFunc {
	params := f.Signature.Params().Len()
	return genericFunc{
		sinks:  make([]bool, params),
		taints: map[int][]int{},
	}
}

func (g genericFunc) Sinks(arg int) bool {
	return arg < len(g.sinks) && g.sinks[arg]
}

func (g genericFunc) Taints(args ...int) []int {
	union := map[int]bool{}
	for _, a := range args {
		for _, t := range g.taints[a] {
			union[t] = true
		}
	}
	var tainted []int
	for a := range union {
		tainted = append(tainted, a)
	}
	return tainted
}

func (g genericFunc) String() string {
	var b strings.Builder
	b.WriteString("genericFunc{ sinks: [")
	for i, reachesSink := range g.sinks {
		if reachesSink {
			b.WriteString(strconv.Itoa(i))
			if i < len(g.sinks)-1 {
				b.WriteByte(' ')
			}
		}
	}
	b.WriteString("], taints: ")
	b.WriteString(fmt.Sprintf("%v", g.taints))
	b.WriteString(" }")
	return b.String()
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

	retVals := findRetvals(f)

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

func findRetvals(f *ssa.Function) map[ssa.Value]int {
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
	}
	return retvals
}

func visit(p *analysis.Pass, conf *config.Config, retVals map[ssa.Value]int, param *ssa.Parameter) (reachesSink bool, taints []int) {
	// TODO: figure out a way to not use interface{}
	visited := map[interface{}]bool{}
	stack := []interface{}{param}

	for len(stack) > 0 {
		current := stack[len(stack)-1]
		stack = stack[:len(stack)-1]

		switch t := current.(type) {
		case *ssa.Value:
			i, isRet := retVals[*t]
			if isRet {
				taints = append(taints, i)
			}

		case *ssa.Call:
			// TODO: handle methods
			if t.Call.IsInvoke() {
				continue
			}
			f, _ := t.Call.Value.(*ssa.Function)
			fact := &funcFact{}
			hasFact := p.ImportObjectFact(f.Object(), fact)
			if !hasFact {
				analyze(p, conf, f)
			}
			hasFactNow := p.ImportObjectFact(f.Object(), fact)
			if !hasFactNow {
				panic("ʕノ◔ϖ◔ʔノ彡┻━┻")
			}

			switch ff := fact.Function.(type) {
			case sink:
				reachesSink = true
			case sanitizer:
			// stop visiting
			case genericFunc:
				// if func has multiple retvals, will have an extract
				// otherwise func itself is a value so dfsing through it = dfsing through its retval,
				// just don't dfs through its arguments
				switch len(retVals) {
				case 0:
				// stop
				case 1:
					// dfs through
					for i, a := range t.Call.Args {
						if visited[a] {
							reachesSink = reachesSink && ff.Sinks(i)
							argTaints := ff.Taints(i)
							if len(argTaints) == 0 {
								// stop visiting
							}

						}
					}
				default:
					// dfs through
					for i, a := range t.Call.Args {
						if visited[a] {
							reachesSink = reachesSink && ff.Sinks(i)
							argTaints := ff.Taints(i)
							if len(argTaints) == 0 {
								// stop visiting
							}
							// search for Extracts in Referrers and dfs through them if they receive a tainted argument
						}
					}
				}
				// only need to visit tainted return values
			}
		}
	}
	// when you visit a value, check whether it is a return value, if so add its index to the slice of taints

	return reachesSink, taints
}
