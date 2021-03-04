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

// Package cfa implements cross-function analysis. The analyzer
// defined in this package looks at every function in the transitive
// dependencies of the program being analyzed and creates an abstraction
// for each one that can be used to determine what the function does with
// each of its arguments.

package interproc

import (
	"fmt"

	"golang.org/x/tools/go/ssa"
)

// A Function is an abstraction for a Go function.
// It can be queried about what it does with its arguments.
type Function interface {
	// Does this function's nth argument reach a sink?
	Sinks(arg int) bool

	// If this argument is tainted, which return values are tainted?
	Taints(arg int) []int

	fmt.Stringer
}

type sink struct{}

func (s sink) Sinks(_ int) bool {
	return true
}

func (s sink) Taints(_ int) (tainted []int) {
	return
}

func (s sink) String() string {
	return "sink"
}

type sanit struct{}

func (s sanit) Sinks(_ int) bool {
	return false
}

func (s sanit) Taints(_ int) (tainted []int) {
	return
}

func (s sanit) String() string {
	return "sanitizer"
}

type genericFunc struct {
	Sinks_  []bool
	Taints_ [][]int
}

// newGenericFunc returns a genericFunc with its Sinks_ and taints
// fields preallocated to the correct length. The correct length
// is the number of parameters of the given function.
func newGenericFunc(f *ssa.Function) genericFunc {
	params := len(f.Params)
	return genericFunc{
		Sinks_:  make([]bool, params),
		Taints_: make([][]int, params),
	}
}

func (g genericFunc) Sinks(arg int) bool {
	return g.Sinks_[arg]
}

func (g genericFunc) Taints(arg int) (tainted []int) {
	return g.Taints_[arg]
}

func (g genericFunc) String() string {
	// TODO: temporarily satisfy gob encoding
	return "genericFunc"
	//var b strings.Builder
	//b.WriteString("genericFunc{ ")
	//
	//b.WriteString("sinks: <")
	//var reached []string
	//for i, reachesSink := range g.Sinks_ {
	//	if reachesSink {
	//		reached = append(reached, strconv.Itoa(i))
	//	}
	//}
	//b.WriteString(strings.Join(reached, " "))
	//b.WriteByte('>')
	//
	//b.WriteString(", taints: <")
	//var taints []string
	//for _, ts := range g.Taints_ {
	//	sort.Ints(ts)
	//	var tainted []string
	//	for _, t := range ts {
	//		tainted = append(tainted, strconv.Itoa(t))
	//	}
	//	taints = append(taints, fmt.Sprintf("<%v>", strings.Join(tainted, " ")))
	//}
	//b.WriteString(strings.Join(taints, " "))
	//b.WriteString("> }")
	//return b.String()
}
