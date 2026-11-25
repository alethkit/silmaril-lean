// Run from the pinned starlark-go checkout.
package main

import (
	"fmt"
	"strings"

	"go.starlark.net/starlark"
	"go.starlark.net/syntax"
)

func initSource(src string) (starlark.StringDict, error) {
	_, program, err := starlark.SourceProgramOptions(&syntax.FileOptions{}, "calls.star",
		src+"\n", func(string) bool { return false })
	if err != nil {
		return nil, err
	}
	return program.Init(&starlark.Thread{Name: "loop calls"}, nil)
}

func require(ok bool, message string) {
	if !ok {
		panic(message)
	}
}

func main() {
	g, err := initSource(`def append(target, value):
    target.append(value)
def guarded(xs):
    alias = xs
    for x in xs:
        for y in alias:
            break
        append(alias, x)
xs = [1]
guarded(xs)`)
	require(err != nil && strings.Contains(err.Error(), "during iteration"), fmt.Sprint(err))
	xs := g["xs"].(*starlark.List)
	require(xs.Len() == 1 && xs.Append(starlark.None) == nil,
		"module failure must release both iterator guards")
	fmt.Println("PASS distinct alias in callee is guarded until the outer loop exits")

	g, err = initSource(`def append(target, value):
    target.append(value)
def visit(xs, events):
    for x in xs:
        for y in xs:
            append(events, y)
            break
        if x:
            return x
        continue
    return 7
xs = [0, 1, 2]
events = []
out = visit(xs, events)
xs.append(3)`)
	require(err == nil, fmt.Sprint(err))
	require(g["out"].String() == "1" && g["events"].String() == "[0, 0]" &&
		g["xs"].String() == "[0, 1, 2, 3]", "loop flow, effects, or cleanup differed")
	fmt.Println("PASS nested calls keep effects through break, continue, and return")
}
