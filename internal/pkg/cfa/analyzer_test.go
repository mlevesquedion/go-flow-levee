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
	"flag"
	"path/filepath"
	"testing"

	"github.com/google/go-flow-levee/internal/pkg/config"
	"github.com/google/go-flow-levee/internal/pkg/debug"
	"golang.org/x/tools/go/analysis/analysistest"
)

var debugging *bool = flag.Bool("debug", false, "run the debug analyzer")

func TestAnalyzer(t *testing.T) {
	testdata := analysistest.TestData()
	if err := config.FlagSet.Set("config", filepath.Join(testdata, "test-config.json")); err != nil {
		t.Error(err)
	}
	if *debugging {
		Analyzer.Requires = append(Analyzer.Requires, debug.Analyzer)
	}
	analysistest.Run(t, testdata, Analyzer, "example.com/core", "example.com/tests")
}