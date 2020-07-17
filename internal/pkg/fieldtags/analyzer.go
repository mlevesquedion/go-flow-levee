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

// Package fieldtags defines an analyzer that identifies struct fields tagged with datapol annotations
// indicating that they contain SPII.
package fieldtags

import (
	"fmt"
	"go/ast"
	"reflect"
	"regexp"
	"strings"

	"golang.org/x/tools/go/analysis"
	"golang.org/x/tools/go/analysis/passes/inspect"
	"golang.org/x/tools/go/analysis/passes/structtag"
	"golang.org/x/tools/go/ast/inspector"
)

type keyValue struct {
	key   string
	value string
}

func (kv *keyValue) String() string {
	return fmt.Sprintf(`%s:"%s"`, kv.key, kv.value)
}

type keyValueMatcher struct {
	re *regexp.Regexp
}

func newKeyValueMatcher(keyValues *[]keyValue) keyValueMatcher {
	var b strings.Builder
	b.WriteString("(")
	for i, keyValue := range *keyValues {
		b.WriteString(keyValue.String())
		if i+1 < len(*keyValues) {
			b.WriteString("|")
		}
	}
	b.WriteString(")")

	re, err := regexp.Compile(b.String())
	if err != nil {
		panic(err)
	}
	return keyValueMatcher{re}
}

var sourcePatterns = []keyValue{
	{"levee", "source"},
}

var Analyzer = &analysis.Analyzer{
	Name:       "fieldtags",
	Doc:        "This analyzer identifies Source fields based on their tags.",
	Run:        run,
	Requires:   []*analysis.Analyzer{inspect.Analyzer, structtag.Analyzer},
	ResultType: reflect.TypeOf(new([]*ast.Field)).Elem(),
}

func run(pass *analysis.Pass) (interface{}, error) {
	inspect := pass.ResultOf[inspect.Analyzer].(*inspector.Inspector)
	results := []*ast.Field{}

	nodeFilter := []ast.Node{
		(*ast.Field)(nil),
	}

	matcher := newKeyValueMatcher(&sourcePatterns)

	inspect.Preorder(nodeFilter, func(n ast.Node) {
		field, ok := n.(*ast.Field)
		if !ok {
			return
		}
		if matcher.isSource(field) {
			results = append(results, field)
			pass.Reportf(field.Pos(), "tagged field")
		}
	})
	return results, nil
}

func (m *keyValueMatcher) isSource(field *ast.Field) bool {
	if field.Tag == nil {
		return false
	}
	tag := field.Tag.Value
	return m.matches(tag)
}

func (m *keyValueMatcher) matches(tag string) bool {
	return m.re.MatchString(tag)
}
