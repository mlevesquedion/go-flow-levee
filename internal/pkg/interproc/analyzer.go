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

// Package interproc implements interprocedural taint propagation analysis
// using function summaries. A summary of each function's behavior is created,
// such that a function can be queried about what happens if each of its arguments
// is tainted. Specifically:
// * Which (if any) return values are tainted?
// * Does taint reach a sink?
package interproc

import (
	"fmt"
	"go/types"
	"log"
	"reflect"
	"sort"

	"github.com/google/go-flow-levee/internal/pkg/config"
	"github.com/google/go-flow-levee/internal/pkg/fieldtags"
	"github.com/google/go-flow-levee/internal/pkg/sanitizer"
	"github.com/google/go-flow-levee/internal/pkg/sourcetype"
	"github.com/google/go-flow-levee/internal/pkg/utils"
	"golang.org/x/tools/go/analysis"
	"golang.org/x/tools/go/analysis/passes/buildssa"
	"golang.org/x/tools/go/pointer"
	"golang.org/x/tools/go/ssa"
)

// ResultType is a mapping from types.Object to cfa.Function
type ResultType = map[types.Object]Function

type funcFact struct {
	F Function
}

func (ff funcFact) AFact() {}

func (ff funcFact) String() string {
	return ff.F.String()
}

// Dirty hack: this is just so we can force the analysis package to gob.Register
// this type.
func (gf genericFunc) AFact() {}

// Dirty hack: this is just so we can force the analysis package to gob.Register
// this type.
func (s sink) AFact() {}

// Dirty hack: this is just so we can force the analysis package to gob.Register
// this type.
func (s sanit) AFact() {}

var Analyzer = &analysis.Analyzer{
	Name:       "interproc",
	Run:        run,
	Flags:      config.FlagSet,
	Doc:        "interproc",
	Requires:   []*analysis.Analyzer{buildssa.Analyzer, fieldtags.Analyzer},
	ResultType: reflect.TypeOf(new(ResultType)).Elem(),
	// Dirty hack: genericFunc, sink and sanit aren't actually facts, this is just
	// to force the analysis package to gob.Register them
	FactTypes: []analysis.Fact{new(funcFact), new(genericFunc), new(sink), new(sanit)},
}

func run(pass *analysis.Pass) (interface{}, error) {
	ssaInput := pass.ResultOf[buildssa.Analyzer].(*buildssa.SSA)
	taggedFields := pass.ResultOf[fieldtags.Analyzer].(fieldtags.ResultType)
	conf, err := config.ReadConfig()
	if err != nil {
		return nil, err
	}

	var funcsToAnalyze []*ssa.Function
	for _, fn := range ssaInput.SrcFuncs {
		switch {
		case conf.IsSink(utils.DecomposeFunction(fn)) && pass.Pkg == fn.Pkg.Pkg:
			pass.ExportObjectFact(fn.Object(), &funcFact{sink{}})
		case conf.IsSanitizer(utils.DecomposeFunction(fn)) && pass.Pkg == fn.Pkg.Pkg:
			pass.ExportObjectFact(fn.Object(), &funcFact{sanit{}})
		default:
			funcsToAnalyze = append(funcsToAnalyze, fn)
		}
	}

	analyzing := map[*ssa.Function]bool{}
	for _, fn := range funcsToAnalyze {
		analyze(pass, conf, taggedFields, analyzing, fn)
	}

	functions := map[types.Object]Function{}
	for _, f := range pass.AllObjectFacts() {
		ff, _ := f.Fact.(*funcFact)
		functions[f.Object] = ff.F
	}
	return functions, nil
}

func analyze(pass *analysis.Pass, conf *config.Config, taggedFields fieldtags.ResultType, analyzing map[*ssa.Function]bool, fn *ssa.Function) {
	// this function is part of a cycle
	if analyzing[fn] {
		return
	}

	// TODO: pretty sure we don't need to skip methods
	//if fn.Signature.Recv() != nil {
	//	return
	//}

	// some functions do not have objects, so they can't be analyzed
	// e.g. exporting a fact on a nil object is an error
	if fn.Object() == nil {
		return
	}

	// fn.Pkg is nil for shared funcs (according to docs for ssa.Function.Pkg)
	if fn.Pkg == nil || pass.Pkg != fn.Pkg.Pkg {
		return
	}

	analyzing[fn] = true
	gf := analyzeGenericFunc(pass, conf, taggedFields, analyzing, fn)
	pass.ExportObjectFact(fn.Object(), &funcFact{gf})
	analyzing[fn] = false
}

func analyzeGenericFunc(pass *analysis.Pass, conf *config.Config, taggedFields fieldtags.ResultType, analyzing map[*ssa.Function]bool, f *ssa.Function) genericFunc {
	gf := newGenericFunc(f)

	for i, param := range f.Params {
		prop := Taint(param, analyzing, pass, conf, taggedFields)

		gf.Sinks_[i] = prop.reachesSink

		// which return values are tainted by param i?
		// (a retval is considered tainted if it is tainted in at least one return)
		taintedRetval := map[int]bool{}
		for node := range prop.tainted {
			// TODO: prop.IsTainted on Return is an underapproximation, but we can't
			// check for sanitization status on the returned values because they are
			// values (checking sanitization status requires an instruction, because
			// it relies on domination)
			if r, ok := node.(*ssa.Return); ok && prop.IsTainted(r) {
				for i, res := range r.Results {
					if prop.tainted[res.(ssa.Node)] {
						taintedRetval[i] = true
					}
				}
			}
		}
		taints := make([]int, 0, len(taintedRetval))
		for i := range taintedRetval {
			taints = append(taints, i)
		}
		sort.Ints(taints)
		gf.Taints_[i] = taints
	}

	return gf
}

// Propagation represents the information that is used by, and collected
// during, a taint propagation analysis.
type Propagation struct {
	root         ssa.Node
	tainted      map[ssa.Node]bool
	preOrder     []ssa.Node
	reachesSink  bool
	sanitizers   []*sanitizer.Sanitizer
	analyzing    map[*ssa.Function]bool
	pass         *analysis.Pass
	conf         *config.Config
	taggedFields fieldtags.ResultType
}

// Taint performs a depth-first search of the graph formed by SSA Referrers and
// Operands relationships, beginning at the given root node.
func Taint(n ssa.Node, analyzing map[*ssa.Function]bool, pass *analysis.Pass, conf *config.Config, taggedFields fieldtags.ResultType) Propagation {
	prop := Propagation{
		root:         n,
		tainted:      make(map[ssa.Node]bool),
		analyzing:    analyzing,
		pass:         pass,
		conf:         conf,
		taggedFields: taggedFields,
	}
	maxInstrReached := map[*ssa.BasicBlock]int{}

	prop.taint(n, maxInstrReached, nil, false)
	// ensure immediate referrers are visited
	prop.taintReferrers(n, maxInstrReached, nil)

	return prop
}

// taint performs a depth-first search of the graph formed by SSA Referrers and
// Operands relationships. Along the way, visited nodes are marked and stored
// in a slice which captures the visitation order. Sanitizers are also recorded.
// maxInstrReached and lastBlockVisited are used to give the traversal some
// degree of flow sensitivity. Specifically:
// - maxInstrReached records the highest index of an instruction visited
//   in each block. This is used to avoid visiting past instructions, e.g.
//   a call to a sink where the argument was tainted after the call happened.
// - lastBlockVisited is used to determine whether the next instruction to visit
//   can be reached from the current instruction.
func (prop *Propagation) taint(n ssa.Node, maxInstrReached map[*ssa.BasicBlock]int, lastBlockVisited *ssa.BasicBlock, isReferrer bool) {
	if prop.shouldNotTaint(n, maxInstrReached, lastBlockVisited, isReferrer) {
		return
	}
	prop.preOrder = append(prop.preOrder, n)
	prop.tainted[n] = true

	mirCopy := map[*ssa.BasicBlock]int{}
	for m, i := range maxInstrReached {
		mirCopy[m] = i
	}

	if instr, ok := n.(ssa.Instruction); ok {
		instrIndex, ok := indexInBlock(instr)
		if !ok {
			return
		}

		if mirCopy[instr.Block()] < instrIndex {
			mirCopy[instr.Block()] = instrIndex
		}

		lastBlockVisited = instr.Block()
	}

	prop.taintNeighbors(n, mirCopy, lastBlockVisited)
}

func (prop *Propagation) shouldNotTaint(n ssa.Node, maxInstrReached map[*ssa.BasicBlock]int, lastBlockVisited *ssa.BasicBlock, isReferrer bool) bool {
	if prop.tainted[n] {
		return true
	}

	if !hasTaintableType(n) {
		return true
	}

	if instr, ok := n.(ssa.Instruction); ok {
		instrIndex, ok := indexInBlock(instr)
		if !ok {
			return true
		}

		// If the referrer is in a different block from the one we last visited,
		// and it can't be reached from the block we are visiting, then stop visiting.
		if lastBlockVisited != nil && instr.Block() != lastBlockVisited && !prop.canReach(lastBlockVisited, instr.Block()) {
			return true
		}

		// If this call's index is lower than the highest seen so far in its block,
		// then this call is "in the past". If this call is a referrer,
		// then we would be propagating taint backwards in time, so stop traversing.
		// (If the call is an operand, then it is being used as a value, so it does
		// not matter when the call occurred.)
		if _, ok := instr.(*ssa.Call); ok && instrIndex < maxInstrReached[instr.Block()] && isReferrer {
			return true
		}
	}

	return false
}

func (prop *Propagation) taintNeighbors(n ssa.Node, maxInstrReached map[*ssa.BasicBlock]int, lastBlockVisited *ssa.BasicBlock) {
	switch t := n.(type) {
	case *ssa.Alloc:
		// An Alloc represents the allocation of space for a variable. If a Node is an Alloc,
		// and the thing being allocated is not an array, then either:
		// a) it is a Source value, in which case it will get its own traversal when sourcesFromBlocks
		//    finds this Alloc
		// b) it is not a Source value, in which case we should not visit it.
		// However, if the Alloc is an array, then that means the source that we are visiting from
		// is being placed into an array, slice or varargs, so we do need to keep visiting.
		if _, isArray := utils.Dereference(t.Type()).(*types.Array); isArray {
			prop.taintReferrers(n, maxInstrReached, lastBlockVisited)
		}

	case *ssa.Call:
		prop.taintCall(t, maxInstrReached, lastBlockVisited)

	case *ssa.Field:
		prop.taintField(n, maxInstrReached, lastBlockVisited, t.X.Type(), t.Field)

	case *ssa.FieldAddr:
		prop.taintField(n, maxInstrReached, lastBlockVisited, t.X.Type(), t.Field)

	// Everything but the actual integer Index should be visited.
	case *ssa.Index:
		prop.taintReferrers(n, maxInstrReached, lastBlockVisited)
		prop.taint(t.X.(ssa.Node), maxInstrReached, lastBlockVisited, false)

	// Everything but the actual integer Index should be visited.
	case *ssa.IndexAddr:
		prop.taintReferrers(n, maxInstrReached, lastBlockVisited)
		prop.taint(t.X.(ssa.Node), maxInstrReached, lastBlockVisited, false)

	// Only the Addr (the Value that is being written to) should be visited.
	case *ssa.Store:
		prop.taint(t.Addr.(ssa.Node), maxInstrReached, lastBlockVisited, false)

	// Only the Map itself can be tainted by an Update.
	// The Key can't be tainted.
	// The Value can propagate taint to the Map, but not receive it.
	// MapUpdate has no referrers, it is only an Instruction, not a Value.
	case *ssa.MapUpdate:
		prop.taint(t.Map.(ssa.Node), maxInstrReached, lastBlockVisited, false)

	case *ssa.Select:
		prop.taintSelect(t, maxInstrReached, lastBlockVisited)

	// The only Operand that can be tainted by a Send is the Chan.
	// The Value can propagate taint to the Chan, but not receive it.
	// Send has no referrers, it is only an Instruction, not a Value.
	case *ssa.Send:
		prop.taint(t.Chan.(ssa.Node), maxInstrReached, lastBlockVisited, false)

	case *ssa.Slice:
		prop.taintReferrers(n, maxInstrReached, lastBlockVisited)
		// This allows taint to propagate backwards into the sliced value
		// when the resulting value is tainted
		prop.taint(t.X.(ssa.Node), maxInstrReached, lastBlockVisited, false)

	// These nodes' operands should not be visited, because they can only receive
	// taint from their operands, not propagate taint to them.
	case *ssa.BinOp, *ssa.ChangeInterface, *ssa.ChangeType, *ssa.Convert, *ssa.Extract, *ssa.MakeChan, *ssa.MakeMap, *ssa.MakeSlice, *ssa.Phi, *ssa.Range:
		prop.taintReferrers(n, maxInstrReached, lastBlockVisited)

	// These nodes don't have operands; they are Values, not Instructions.
	case *ssa.Const, *ssa.FreeVar, *ssa.Global, *ssa.Lookup, *ssa.Parameter:
		prop.taintReferrers(n, maxInstrReached, lastBlockVisited)

	// These nodes don't have referrers; they are Instructions, not Values.
	case *ssa.Go:
		prop.taintOperands(n, maxInstrReached, lastBlockVisited)

	// These nodes are both Instructions and Values, and currently have no special restrictions.
	case *ssa.MakeInterface, *ssa.TypeAssert, *ssa.UnOp:
		prop.taintReferrers(n, maxInstrReached, lastBlockVisited)
		prop.taintOperands(n, maxInstrReached, lastBlockVisited)

	// These nodes cannot propagate taint.
	case *ssa.Builtin, *ssa.DebugRef, *ssa.Defer, *ssa.Function, *ssa.If, *ssa.Jump, *ssa.MakeClosure, *ssa.Next, *ssa.Panic, *ssa.Return, *ssa.RunDefers:

	default:
		fmt.Printf("unexpected node received: %T %v; please report this issue\n", n, n)
	}
}

func (prop *Propagation) taintField(n ssa.Node, maxInstrReached map[*ssa.BasicBlock]int, lastBlockVisited *ssa.BasicBlock, t types.Type, field int) {
	if !prop.conf.IsSourceField(utils.DecomposeField(t, field)) && !prop.taggedFields.IsSourceField(t, field) {
		return
	}
	prop.taintReferrers(n, maxInstrReached, lastBlockVisited)
	prop.taintOperands(n, maxInstrReached, lastBlockVisited)
}

func (prop *Propagation) taintReferrers(n ssa.Node, maxInstrReached map[*ssa.BasicBlock]int, lastBlockVisited *ssa.BasicBlock) {
	if n.Referrers() == nil {
		return
	}
	for _, r := range *n.Referrers() {
		prop.taint(r.(ssa.Node), maxInstrReached, lastBlockVisited, true)
	}
}

func (prop *Propagation) taintOperands(n ssa.Node, maxInstrReached map[*ssa.BasicBlock]int, lastBlockVisited *ssa.BasicBlock) {
	for _, o := range n.Operands(nil) {
		if *o == nil {
			continue
		}
		prop.taint((*o).(ssa.Node), maxInstrReached, lastBlockVisited, false)
	}
}

func (prop *Propagation) taintCall(call *ssa.Call, maxInstrReached map[*ssa.BasicBlock]int, lastBlockVisited *ssa.BasicBlock) {
	// Some builtins require special handling
	if builtin, ok := call.Call.Value.(*ssa.Builtin); ok {
		prop.taintBuiltin(call, builtin.Name(), maxInstrReached, lastBlockVisited)
		return
	}

	if callee := call.Call.StaticCallee(); callee != nil && prop.conf.IsSanitizer(utils.DecomposeFunction(callee)) {
		prop.sanitizers = append(prop.sanitizers, &sanitizer.Sanitizer{Call: call})
	}

	// Do not traverse through a method call if it is being reached via a Source receiver.
	// Do traverse if the call is being reached through a tainted argument.
	// Source methods that return tainted values regardless of their arguments should be identified by the fieldpropagator analyzer.
	if recv := call.Call.Signature().Recv(); recv != nil && sourcetype.IsSourceType(prop.conf, prop.taggedFields, recv.Type()) {
		// If the receiver is not statically known (it has interface type) and the
		// method has no arguments, Args will be empty.
		if len(call.Call.Args) == 0 {
			return
		}
		visitingFromArg := false
		for i, a := range call.Call.Args {
			// If the receiver's type is statically known,
			// it will be the first element of the Args slice.
			if !call.Call.IsInvoke() && i == 0 {
				continue
			}
			if prop.tainted[a.(ssa.Node)] {
				visitingFromArg = true
			}
		}
		if !visitingFromArg {
			// unmark the node so that it may be visited again when taint propagates to an argument
			prop.tainted[call] = false
			return
		}
	}

	f := call.Call.StaticCallee()

	// TODO: Assume non-static calls are safe.
	//       This is a pretty big underapproximation, but may be pragmatic.
	//       In future, we will likely want to identify candidate callees,
	//       analyze all of them, and take the union as summary.
	if f == nil || f.Object() == nil {
		return
	}

	fact := &funcFact{}
	hasFact := prop.pass.ImportObjectFact(f.Object(), fact)
	if !hasFact {
		analyze(prop.pass, prop.conf, prop.taggedFields, prop.analyzing, f)
	}

	hasFactNow := prop.pass.ImportObjectFact(f.Object(), fact)
	// the function being called is part of a cycle in the call graph
	// assume we should keep traversing
	// (this overapproximates)
	if !hasFactNow {
		prop.taintReferrers(call, maxInstrReached, lastBlockVisited)
		return
	}

	funcSummary := fact.F

	// find answers to:
	//   - have we reached a sink?
	//   - which return values are tainted, given the taint status of the args?
	// TODO: This underapproximates, because a call won't be visited twice, but
	//       a call may be reached through more than one taint propagation path,
	//       so we should actually avoid analyzing a call until we have determined
	//       the taint status of all of its arguments.
	// TODO: I'm pretty sure the way this identifies extracts to traverse to could
	//       be simplified.
	taintedRetvals := map[int]bool{}
	for i, a := range call.Call.Args {
		// if we've visited this argument, then we are on a path from the current parameter to this call
		if prop.tainted[a.(ssa.Node)] {
			prop.reachesSink = prop.reachesSink || funcSummary.Sinks(i)
			for _, j := range funcSummary.Taints(i) {
				taintedRetvals[j] = true
			}
		}
	}

	// this should never occur, but let's make sure we don't panic
	if call.Referrers() == nil {
		return
	}
	// a function call will have extracts if the function
	// returns more than 1 value
	extracts := map[int]*ssa.Extract{}
	for _, r := range *call.Referrers() {
		if e, ok := r.(*ssa.Extract); ok {
			extracts[e.Index] = e
		}
	}

	switch {
	// function has one return value and it is tainted
	case len(extracts) == 0 && len(taintedRetvals) == 1:
		prop.taintReferrers(call, maxInstrReached, lastBlockVisited)
	// function has multiple return values and they
	// are extracted from the call
	case len(extracts) > 0:
		for i := range taintedRetvals {
			prop.taint(extracts[i], maxInstrReached, lastBlockVisited, true)
		}
	}

	// TODO: for now, assume colocated args can't be tainted (underapproximation)
	// TODO: this can be handled later, i.e. by checking which params are reachable
	//       from each param
	//for _, a := range call.Call.Args {
	//	prop.taintCallArg(a, maxInstrReached, lastBlockVisited)
	//}
	//prop.taintOperands(call, maxInstrReached, lastBlockVisited)

	// TODO: exception to the above: we have to assume that the receiver is tainted
	//       otherwise calls to e.g. fmt.Sprintf won't register
	//if recv := call.Call.Signature().Recv(); recv != nil {
	//	prop.taint(call.Call.Args[0].(ssa.Node), maxInstrReached, lastBlockVisited, true)
	//}
}

func (prop *Propagation) taintBuiltin(c *ssa.Call, builtinName string, maxInstrReached map[*ssa.BasicBlock]int, lastBlockVisited *ssa.BasicBlock) {
	switch builtinName {
	// The values being appended cannot be tainted.
	case "append":
		// The slice argument needs to be tainted because if its underlying array has
		// enough remaining capacity, the appended values will be written to it.
		prop.taintCallArg(c.Call.Args[0], maxInstrReached, lastBlockVisited)
		// The returned slice is tainted if either the slice argument or the values
		// are tainted, so we need to visit the referrers.
		prop.taintReferrers(c, maxInstrReached, lastBlockVisited)
	// Only the first argument (dst) can be tainted. (The src cannot be tainted.)
	case "copy":
		prop.taintCallArg(c.Call.Args[0], maxInstrReached, lastBlockVisited)
	// The builtin delete(m map[Type]Type1, key Type) func does not propagate taint.
	case "delete":
	}
}

func (prop *Propagation) taintCallArg(arg ssa.Value, maxInstrReached map[*ssa.BasicBlock]int, lastBlockVisited *ssa.BasicBlock) {
	if canBeTaintedByCall(arg.Type()) {
		prop.taint(arg.(ssa.Node), maxInstrReached, lastBlockVisited, false)
	}
}

func (prop *Propagation) taintSelect(sel *ssa.Select, maxInstrReached map[*ssa.BasicBlock]int, lastBlockVisited *ssa.BasicBlock) {
	// Select returns a tuple whose first 2 elements are irrelevant for our
	// analysis. Subsequent elements correspond to Recv states, which map
	// 1:1 with Extracts.
	// See the ssa package code for more details.
	recvIndex := 0
	extractIndex := map[*ssa.SelectState]int{}
	for _, ss := range sel.States {
		if ss.Dir == types.RecvOnly {
			extractIndex[ss] = recvIndex + 2
			recvIndex++
		}
	}

	for _, s := range sel.States {
		switch {
		// If the sent value (Send) is tainted, propagate taint to the channel
		case s.Dir == types.SendOnly && prop.tainted[s.Send.(ssa.Node)]:
			prop.taint(s.Chan.(ssa.Node), maxInstrReached, lastBlockVisited, false)

		// If the channel is tainted, propagate taint to the appropriate Extract
		case s.Dir == types.RecvOnly && prop.tainted[s.Chan.(ssa.Node)]:
			if sel.Referrers() == nil {
				continue
			}
			for _, r := range *sel.Referrers() {
				e, ok := r.(*ssa.Extract)
				if !ok || e.Index != extractIndex[s] {
					continue
				}
				prop.taint(e, maxInstrReached, lastBlockVisited, false)
			}
		}
	}
}

func (prop *Propagation) canReach(start *ssa.BasicBlock, dest *ssa.BasicBlock) bool {
	if start.Dominates(dest) {
		return true
	}

	stack := stack([]*ssa.BasicBlock{start})
	seen := map[*ssa.BasicBlock]bool{start: true}
	for len(stack) > 0 {
		current := stack.pop()
		if current == dest {
			return true
		}
		for _, s := range current.Succs {
			if seen[s] {
				continue
			}
			seen[s] = true
			stack.push(s)
		}
	}
	return false
}

// IsTainted determines whether an instruction is tainted by the Propagation.
func (prop Propagation) IsTainted(instr ssa.Instruction) bool {
	return prop.tainted[instr.(ssa.Node)] && !prop.isSanitizedAt(instr)
}

// isSanitizedAt determines whether the taint propagated from the Propagation's root
// is sanitized when it reaches the target instruction.
func (prop Propagation) isSanitizedAt(instr ssa.Instruction) bool {
	for _, san := range prop.sanitizers {
		if san.Dominates(instr) {
			return true
		}
	}

	return false
}

type stack []*ssa.BasicBlock

func (s *stack) pop() *ssa.BasicBlock {
	if len(*s) == 0 {
		log.Println("tried to pop from empty stack")
	}
	popped := (*s)[len(*s)-1]
	*s = (*s)[:len(*s)-1]
	return popped
}

func (s *stack) push(b *ssa.BasicBlock) {
	*s = append(*s, b)
}

// indexInBlock returns this instruction's index in its parent block.
func indexInBlock(target ssa.Instruction) (int, bool) {
	for i, instr := range target.Block().Instrs {
		if instr == target {
			return i, true
		}
	}
	// we can only hit this return if there is a bug in the ssa package
	// i.e. an instruction does not appear within its parent block
	return 0, false
}

func hasTaintableType(n ssa.Node) bool {
	if v, ok := n.(ssa.Value); ok {
		switch t := v.Type().(type) {
		case *types.Basic:
			return t.Info() != types.IsBoolean
		case *types.Signature:
			return false
		}
	}
	return true
}

// A type can be tainted by a call if it is itself a pointer or pointer-like type (according to
// pointer.CanPoint), or it is an array/struct that holds an element that can be tainted by
// a call.
func canBeTaintedByCall(t types.Type) bool {
	if pointer.CanPoint(t) {
		return true
	}

	switch tt := t.(type) {
	case *types.Array:
		return canBeTaintedByCall(tt.Elem())

	case *types.Struct:
		for i := 0; i < tt.NumFields(); i++ {
			// this cannot cause an infinite loop, because a struct
			// type cannot refer to itself except through a pointer
			if canBeTaintedByCall(tt.Field(i).Type()) {
				return true
			}
		}
		return false
	}

	return false
}
