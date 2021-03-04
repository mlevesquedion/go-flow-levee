package interproc

import (
	"path/filepath"
	"testing"

	"golang.org/x/tools/go/analysis/analysistest"
)

func TestAnalyzer(t *testing.T) {
	testdata := analysistest.TestData()
	if err := Analyzer.Flags.Set("config", filepath.Join(testdata, "/test-config.yaml")); err != nil {
		t.Error(err)
	}
	analysistest.Run(t, testdata, Analyzer, "./...")
}
