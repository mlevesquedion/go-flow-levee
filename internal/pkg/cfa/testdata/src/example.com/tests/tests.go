package cfa

import (
	"example.com/core"
)

func OneParamSinkWrapper(a interface{}) { // want OneParamSinkWrapper:"genericFunc{ sinks: \\[0\\], taints: \\[\\[\\]\\] }"
	core.Sink(a)
}
