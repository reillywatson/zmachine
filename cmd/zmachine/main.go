package main

import (
	"encoding/base64"
	"github.com/reillywatson/zmachine"
	"io/ioutil"
	"os"
)

func main() {
	var buffer []byte
	var err error
	if len(os.Args) != 2 {
		buffer, err = base64.StdEncoding.DecodeString(zmachine.Zork)
	} else {
		buffer, err = ioutil.ReadFile(os.Args[1])
	}
	if err != nil {
		panic(err)
	}
	var header zmachine.ZHeader
	header.Read(buffer)

	if header.Version != 3 {
		panic("Only Version 3 files supported")
	}

	var zm zmachine.ZMachine
	zm.Initialize(buffer, header)

	for !zm.Done {
		zm.InterpretInstruction()
	}
}
