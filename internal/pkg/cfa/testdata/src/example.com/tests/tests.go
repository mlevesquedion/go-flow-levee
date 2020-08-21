package cfa

import (
	"example.com/core"
)

func OneParamSinkWrapper(a interface{}) { // want OneParamSinkWrapper:"genericFunc{ sinks: \\[0\\], taints: \\[\\[\\]\\] }"
	core.Sink(a)
}

func TwoParamSinkWrapper(a interface{}, b interface{}) { // want TwoParamSinkWrapper:"genericFunc{ sinks: \\[0 1\\], taints: \\[\\[\\] \\[\\]\\] }"
	core.Sink(a)
	core.Sink(b)
}

func OneParamSanitizedBeforeSinkCall(a interface{}) { // want OneParamSanitizedBeforeSinkCall:"genericFunc{ sinks: \\[\\], taints: \\[\\[\\]\\] }"
	s := core.Sanitize(a)
	core.Sink(s)
}

func OneParamSanitizedBeforeReturn(a interface{}) interface{} { // want OneParamSanitizedBeforeReturn:"genericFunc{ sinks: \\[\\], taints: \\[\\[\\]\\] }"
	s := core.Sanitize(a)
	return s
}

func OneParamTaintingOneResult(a interface{}) interface{} { // want OneParamTaintingOneResult:"genericFunc{ sinks: \\[\\], taints: \\[\\[0\\]\\] }"
	return a
}

func OneParamTaintingBothResults(a interface{}) (interface{}, interface{}) { // want OneParamTaintingBothResults:"genericFunc{ sinks: \\[\\], taints: \\[\\[0 1\\]\\] }"
	return a, a
}

func OneParamTaintingOneOfTwoResults(a interface{}) (interface{}, interface{}) { // want OneParamTaintingOneOfTwoResults:"genericFunc{ sinks: \\[\\], taints: \\[\\[1\\]\\] }"
	return nil, a
}

func TwoParamsEachTaintingOneResult(a interface{}, b interface{}) (interface{}, interface{}) { // want TwoParamsEachTaintingOneResult:"genericFunc{ sinks: \\[\\], taints: \\[\\[1\\] \\[0\\]\\] }"
	return b, a
}

func SinkWrapper(a interface{}, b interface{}) (interface{}, interface{}) { // want SinkWrapper:"genericFunc{ sinks: \\[0\\], taints: \\[\\[\\] \\[0\\]\\] }"
	core.Sink(a)
	sanitized := core.Sanitize(a)
	tainted := []interface{}{b}
	return tainted, sanitized
}

func SinkWrapperWrapper(c interface{}) { // want SinkWrapperWrapper:"genericFunc{ sinks: \\[0\\], taints: \\[\\[\\]\\] }"
	SinkWrapper(c, "")
}

func SinkWrapperWrapperWrapper(d interface{}, e interface{}) { // want SinkWrapperWrapperWrapper:"genericFunc{ sinks: \\[0 1\\], taints: \\[\\[\\] \\[\\]\\] }"
	SinkWrapper(d, "d")
	SinkWrapper(e, "e")
}

func SinksFive(a interface{}) { // want SinksFive:"genericFunc{ sinks: \\[\\], taints: \\[\\[\\]\\] }"
	five := ReturnsFive(a)
	core.Sink(five)
}

func ReturnsFive(a interface{}) int { // want ReturnsFive:"genericFunc{ sinks: \\[\\], taints: \\[\\[\\]\\] }"
	return 5
}

func SinksThroughIdentity(a interface{}) { // want SinksThroughIdentity:"genericFunc{ sinks: \\[0\\], taints: \\[\\[\\]\\] }"
	i := Identity(a)
	core.Sink(i)
}

func Identity(a interface{}) interface{} { // want Identity: "genericFunc{ sinks: \\[\\], taints: \\[\\[0\\]\\] }"
	return a
}
