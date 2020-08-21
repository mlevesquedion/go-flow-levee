package tests

import "example.com/core"

// this regex matching in wants can be a bit of a pain sometimes...
func SinkWrapper(a interface{}, b interface{}) (interface{}, interface{}) { // want SinkWrapper:"genericFunc{ sinks: \\[0\\], taints: \\[\\[\\] \\[0\\]\\] }"
	core.Sink(a)
	sanitized := core.Sanitize(a)
	tainted := []interface{}{b}
	return tainted, sanitized
}

func SinkWrapperWrapper(e interface{}) { // want SinkWrapperWrapper:"genericFunc{ sinks: \\[0\\], taints: \\[\\[\\]\\] }"
	SinkWrapper(e, "whatever")
}
