// Run from the pinned starlark-go checkout.
package main

import (
	"fmt"
	"strings"

	"go.starlark.net/starlark"
	"go.starlark.net/syntax"
)

func initSource(src string) (starlark.StringDict, error) {
	_, program, err := starlark.SourceProgramOptions(&syntax.FileOptions{}, "expressions.star",
		src+"\n", func(string) bool { return false })
	if err != nil {
		return nil, err
	}
	return program.Init(&starlark.Thread{Name: "nested calls"}, nil)
}

func require(ok bool, message string) {
	if !ok {
		panic(message)
	}
}

func main() {
	g, err := initSource(`def mark(events, value):
    events.append(value)
    return value
def dispatch(events):
    events.append(0)
    return collect
def collect(a, b, c=0, d=0):
    return (a, b, c, d)
events = []
out = dispatch(events)(events.append(1), c=mark(events, 2), *mark(events, [3]), **mark(events, {"d": 4}))
`)
	require(err == nil, fmt.Sprint(err))
	require(g["out"].String() == "(None, 3, 2, 4)" && g["events"].String() == `[0, 1, 2, [3], {"d": 4}]`,
		"nested callee and operand order differed")
	fmt.Println("PASS callee, atomic and nested operands, keywords and expansions retain source order")

	g, err = initSource(`def visit():
    out = 0
    for i in [1]:
        out = (len([9]) or len(42)) if len([8]) else len(42)
    return out
out = visit()
`)
	require(err == nil && g["out"].String() == "1", fmt.Sprint(err))
	fmt.Println("PASS lazy conditional and short-circuit operands inside a loop")

	g, err = initSource(`def mark(events, value):
    events.append(value)
    return value
def fail_after_mark(events):
    out = 7
    out = 1 and len(mark(events, 5))
    return out
events = []
fail_after_mark(events)
`)
	require(err != nil && strings.Contains(err.Error(), "has no len"), fmt.Sprint(err))
	require(g["events"].String() == "[5]", "prior operand effect was lost")
	fmt.Println("PASS failure in a nested right operand retains effects of earlier evaluation")

	g, err = initSource(`events = []
out = len(len(events.append(1)), events.append(2))
`)
	require(err != nil && strings.Contains(err.Error(), "has no len"), fmt.Sprint(err))
	require(g["events"].String() == "[1]" && g["out"] == nil,
		"the first operand's failure must skip the later operand and destination write")
	fmt.Println("PASS nested positional call failure retains earlier effects and skips later operands")

	g, err = initSource(`events = []
out = events.append(1) and len(events.append(2))
`)
	require(err == nil && g["out"] == starlark.None && g["events"].String() == "[1]",
		"short-circuit must keep the left value and skip both the right effect and failure")
	fmt.Println("PASS skipped call leaves the first mutation and None result")
}
