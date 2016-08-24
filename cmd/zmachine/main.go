package main

import (
	"fmt"
	"github.com/reillywatson/zmachine"
	"io/ioutil"
	"os"
)

func main() {
	if len(os.Args) != 2 {
		fmt.Println("Usage: zmachine <filename>")
		os.Exit(1)
	}
	buffer, err := ioutil.ReadFile(os.Args[1])
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
