package iscsi

import (
	"fmt"

	"example.com/core"
)

type iscsiMounter struct {
	secret map[string]string
}

func AttachDisk(b iscsiMounter) error { // want AttachDisk:"genericFunc{ sinks: <0>, taints: <<>> }"
	if err := updateISCSINode(b); err != nil {
		core.Sinkf("iscsi error:\n%v", err)
	}
}

func updateISCSINode(b iscsiMounter) error { // want updateISCSINode:"genericFunc{ sinks: <>, taints: <<0>> }"
	v := b.secret["password"]
	return fmt.Errorf("here's a secret: %v", v)
}
