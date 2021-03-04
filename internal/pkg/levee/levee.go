// Copyright 2019 Google LLC
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

package internal

import (
	"fmt"
	"strings"

	"github.com/google/go-flow-levee/internal/pkg/config"
	"github.com/google/go-flow-levee/internal/pkg/fieldtags"
	"github.com/google/go-flow-levee/internal/pkg/interproc"
	"github.com/google/go-flow-levee/internal/pkg/propagation"
	"github.com/google/go-flow-levee/internal/pkg/source"
	"golang.org/x/tools/go/analysis"
	"golang.org/x/tools/go/ssa"
)

var Analyzer = &analysis.Analyzer{
	Name:     "levee",
	Run:      run,
	Flags:    config.FlagSet,
	Doc:      "reports attempts to source data to sinks",
	Requires: []*analysis.Analyzer{interproc.Analyzer, source.Analyzer, fieldtags.Analyzer},
}

func run(pass *analysis.Pass) (interface{}, error) {
	conf, err := config.ReadConfig()
	if err != nil {
		return nil, err
	}
	funcSources := pass.ResultOf[source.Analyzer].(source.ResultType)
	taggedFields := pass.ResultOf[fieldtags.Analyzer].(fieldtags.ResultType)
	funcSummaries := pass.ResultOf[interproc.Analyzer].(interproc.ResultType)

	reported := map[ssa.Instruction]bool{}

	for fn, sources := range funcSources {
		propagations := make(map[*source.Source]propagation.Propagation, len(sources))
		for _, s := range sources {
			prop := propagation.Taint(s.Node, conf, taggedFields, funcSummaries)
			propagations[s] = prop
			for _, sink := range prop.ReachedSinks {
				// take sanitization into account
				if !prop.IsTainted(sink) || reported[sink] {
					continue
				}
				reported[sink] = true
				report(conf, pass, s, sink)
			}
		}

		for _, b := range fn.Blocks {
			for _, instr := range b.Instrs {
				switch instr.(type) {
				case *ssa.Panic:
					if conf.AllowPanicOnTaintedValues || reported[instr] {
						continue
					}
					reported[instr] = true
					reportSourcesReachingSink(conf, pass, propagations, instr)
				}
			}
		}
	}

	return nil, nil
}

func reportSourcesReachingSink(conf *config.Config, pass *analysis.Pass, propagations map[*source.Source]propagation.Propagation, sink ssa.Instruction) {
	for src, prop := range propagations {
		if prop.IsTainted(sink) {
			report(conf, pass, src, sink.(ssa.Node))
			break
		}
	}
}

func report(conf *config.Config, pass *analysis.Pass, source *source.Source, sink ssa.Node) {
	var b strings.Builder
	b.WriteString("a source has reached a sink")
	fmt.Fprintf(&b, "\n source: %v", pass.Fset.Position(source.Pos()))
	if conf.ReportMessage != "" {
		fmt.Fprintf(&b, "\n %v", conf.ReportMessage)
	}
	pass.Reportf(sink.Pos(), b.String())
}
