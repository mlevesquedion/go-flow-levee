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

package crossfunc

import (
	"fmt"

	"example.com/core"
)

func TestSinkWrapperWrapper(s core.Source) {
	SinkWrapperWrapper(s) // want "a source has reached a sink, sink:"
}

func SinkWrapperWrapper(arg interface{}) {
	SinkWrapper(arg)
}

func TestSinkWrapper(s core.Source) {
	SinkWrapper(s) // want "a source has reached a sink, sink:"
}

func SinkWrapper(arg interface{}) {
	core.Sink(arg)
}

func TestSinkWrapperTwoArgs(s core.Source) {
	SinkWrapperTwoArgs("not a source", s) // want "a source has reached a sink, sink:"
}

func SinkWrapperTwoArgs(a1 interface{}, a2 interface{}) {
	core.Sink(a1, a2)
}

func TestOneArgSinkWrapper(s core.Source) {
	OneArgSinkWrapper(s) // want "a source has reached a sink, sink:"
}

func OneArgSinkWrapper(arg interface{}) {
	core.OneArgSink(arg)
}

func TestSinkWrapperSlice(s core.Source) {
	SinkWrapperSlice("not a source", s, 0) // want "a source has reached a sink"
}

func SinkWrapperSlice(args ...interface{}) {
	core.Sink(args)
}

func TestSinkWrapperSpread(s core.Source) {
	SinkWrapperSpread("not a source", s, 0) // want "a source has reached a sink"
}

func SinkWrapperSpread(args ...interface{}) {
	core.Sink(args...)
}

func TestStringify(s core.Source) {
	str := Stringify(s)
	core.Sink(str) // want "a source has reached a sink, source:"
}

func Stringify(arg interface{}) string {
	return fmt.Sprintf("%v", arg)
}

func TestReturnsFive(s core.Source) {
	five := ReturnsFive(s)
	core.Sink(five)
}

func ReturnsFive(arg interface{}) int {
	return 5
}
