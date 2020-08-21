// Copyright 2020 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package cfa

import (
	"go/types"
	"reflect"
	"strings"

	"github.com/google/go-flow-levee/internal/pkg/utils"

	"github.com/google/go-flow-levee/internal/pkg/config"
	"golang.org/x/tools/go/analysis"
	"golang.org/x/tools/go/analysis/passes/buildssa"
	"golang.org/x/tools/go/ssa"
)

// ResultType is a mapping from types.Object to cfa.Function
type ResultType = Functions

// Functions is a mapping from types.Object to cfa.Function
type Functions map[types.Object]Function

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
	"bytealg",
	"internal",
	"sync",
	"runtime",
	"unsafe",
	"cpu",
	"sys",
	"reflect",
	"reflectlite",
}

func run(pass *analysis.Pass) (interface{}, error) {
	pkgName := pass.Pkg.Name()
	for _, d := range pkgDenylist {
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
		ff, ok := f.Fact.(*funcFact)
		if !ok {
			continue
		}
		functions[f.Object] = ff.Function
	}
	return Functions(functions), nil
}

func analyze(pass *analysis.Pass, conf *config.Config, fn *ssa.Function) {
	if fn.Signature.Recv() != nil {
		return
	}
	// this function is in a denylisted packaged; exporting a fact on another package's objects is an error
	// some functions do not have objects
	if fn.Pkg.Pkg != pass.Pkg || fn.Object() == nil {
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

	valTaints, results := findValTaints(f)
	gf.results = results

	for i, param := range f.Params {
		reachesSink, taints := visit(p, c, valTaints, param)
		gf.sinks[i] = reachesSink
		gf.taints[i] = taints
	}

	return gf
}

type visitor struct {
	pass *analysis.Pass
	conf *config.Config
	// needs to be a []int in case a value is returned more than once, e.g. return x, x
	valTaints   map[ssa.Value][]int
	visited     map[ssa.Node]bool
	reachesSink bool
	taints      []int
}

func visit(p *analysis.Pass, conf *config.Config, valTaints map[ssa.Value][]int, param *ssa.Parameter) (reachesSink bool, taints []int) {
	v := visitor{
		pass:      p,
		conf:      conf,
		valTaints: valTaints,
		visited:   map[ssa.Node]bool{},
	}

	v.dfs(param)

	return v.reachesSink, v.taints
}

func (v *visitor) dfs(n ssa.Node) {
	if v.visited[n] {
		return
	}
	v.visited[n] = true

	switch n := n.(type) {
	case *ssa.Return:
		// avoid traversing through the other return values
		return
	case ssa.Value:
		for _, i := range v.valTaints[n] {
			v.taints = append(v.taints, i)
		}
	case *ssa.Call:
		// method call
		if n.Call.IsInvoke() {
			return
		}

		f, ok := n.Call.Value.(*ssa.Function)
		if !ok {
			// assume we should keep traversing
			break
		}

		fact := &funcFact{}
		hasFact := v.pass.ImportObjectFact(f.Object(), fact)
		if !hasFact {
			analyze(v.pass, v.conf, f)
		}
		hasFactNow := v.pass.ImportObjectFact(f.Object(), fact)
		if !hasFactNow {
			// this should only happen if the function being visited is in a denylisted package
			// assume we should keep traversing
			break
		}

		v.visitFunc(n, fact)
		return
	}

	v.visitReferrers(n)
	v.visitOperands(n)
}

func (v *visitor) visitFunc(n *ssa.Call, fact *funcFact) {
	switch ff := fact.Function.(type) {
	case sink:
		v.reachesSink = true
		// value has reached a sink, stop traversing
		return
	case sanitizer:
		// value has been sanitized, stop traversing
		return
	case genericFunc:
		// if the function has 0 results, there is nothing to visit
		// if the function has 1 result, and it taints that result, keep visiting
		// if the function has 2+ results, visit only the ones that are tainted
		switch ff.Results() {
		case 0:
			// function has no return value, stop visiting
			return

		case 1:
			for i, a := range n.Call.Args {
				// if we've visited this argument, then we are on a path from the parameter to this call
				if v.visited[a.(ssa.Node)] {
					v.reachesSink = v.reachesSink || ff.Sinks(i)
					argTaints := ff.Taints(i)
					if len(argTaints) == 0 {
						// this function does not taint its return value, stop traversing
						return
					}
					// since this function has only 1 return value, we know it is tainted
					// only visit the Referrers, since the operands are the function's arguments
					v.visitReferrers(n)
				}
			}

		// 2+ results
		// The results of a function with 2+ results appear as "Extracts" in the ssa.
		// The `ssa.Extract` instruction represents getting a value out of the
		// tuple of results that the function returns.
		default:
			// find extracts and make them accessible by index
			extracts := map[int]*ssa.Extract{}
			for _, r := range *n.Referrers() {
				if e, ok := r.(*ssa.Extract); ok {
					extracts[e.Index] = e
				}
			}
			// function has >= 2 return values, but they are not extracted
			if len(extracts) == 0 {
				return
			}
			taintUnion := map[int]bool{}
			for i, a := range n.Call.Args {
				if v.visited[a.(ssa.Node)] {
					v.reachesSink = v.reachesSink || ff.Sinks(i)
					for _, j := range ff.Taints(i) {
						taintUnion[j] = true
					}
				}
			}
			for i := range taintUnion {
				v.dfs(extracts[i])
			}
		}
	}
}

func (v *visitor) visitReferrers(n ssa.Node) {
	referrers := n.Referrers()
	if referrers != nil {
		for _, r := range *referrers {
			n := r.(ssa.Node)
			v.dfs(n)
		}
	}
}
func (v *visitor) visitOperands(n ssa.Node) {
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

func findValTaints(f *ssa.Function) (valToPos map[ssa.Value][]int, results int) {
	retvals := map[ssa.Value][]int{}
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
			retvals[res] = append(retvals[res], i)
		}
		results = len(ret.Results)
	}
	return retvals, results
}
