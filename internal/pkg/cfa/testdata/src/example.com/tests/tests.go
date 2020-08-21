package main

import "example.com/core"

func SinkWrapper(a interface{}, b interface{}) (interface{}, interface{}) { // want SinkWrapper:"genericFunc{ sinks: [0], taints: map[0:[] 1:[0]] }"
	core.Sink(a)
	sanitized := core.Sanitize(a)
	return b, sanitized
}
