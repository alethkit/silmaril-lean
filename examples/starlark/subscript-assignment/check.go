// Run from the pinned starlark-go checkout.
package main

import (
	"fmt"
	"strings"

	"go.starlark.net/starlark"
	"go.starlark.net/syntax"
)

const setup = `def note(marker, value):
    events.append(marker)
    return value
events = []
`

const list = "target = [7]\nalias = target\n"
const dictionary = "target = {\"b\": 7, \"a\": 8}\nalias = target\n"

func require(ok bool, message string) {
	if !ok {
		panic(message)
	}
}

func run(body string, predeclared starlark.StringDict) (starlark.StringDict, error) {
	_, program, err := starlark.SourceProgramOptions(&syntax.FileOptions{}, "assignment.star",
		setup+body+"\n", predeclared.Has)
	if err != nil {
		return nil, err
	}
	return program.Init(&starlark.Thread{Name: "subscript assignment"}, predeclared)
}

func failedWrite(body, message, trace, old string, predeclared starlark.StringDict) starlark.Value {
	g, err := run(body+"\nnote(99, 0)\n", predeclared)
	require(err != nil && strings.Contains(err.Error(), message), fmt.Sprint(err))
	require(g["events"].String() == trace && g["target"].String() == old && g["target"] == g["alias"], body)
	return g["target"]
}

func main() {
	g, err := run(list+`def grow():
    events.append(3)
    alias.append(77)
    return -1
note(2, alias)[grow()] = note(1, 9)`, nil)
	require(err == nil && g["events"].String() == "[1, 2, 3]" && g["target"].String() == "[7, 9]" &&
		g["target"] == g["alias"], fmt.Sprint(err))
	g, err = run(dictionary+`note(2, alias)[note(3, "b")] = note(1, 9)
note(2, alias)[note(3, "c")] = note(1, 9)`, nil)
	require(err == nil && g["events"].String() == "[1, 2, 3, 1, 2, 3]" &&
		g["target"].String() == `{"b": 9, "a": 8, "c": 9}` && g["target"] == g["alias"], fmt.Sprint(err))
	fmt.Println("PASS RHS, receiver and subscript order, aliased writes, and post-operand list length")

	for _, test := range []struct{ stmt, trace, message string }{
		{`note(2, alias)[note(3, 0)] = len(note(1, 9))`, "[1]", "has no len"},
		{`len(note(2, 9))[note(3, 0)] = note(1, 9)`, "[1, 2]", "has no len"},
		{`note(2, alias)[len(note(3, 9))] = note(1, 9)`, "[1, 2, 3]", "has no len"},
		{`note(2, 7)[note(3, 0)] = note(1, 9)`, "[1, 2, 3]", "does not support item assignment"},
	} {
		failedWrite(list+test.stmt, test.message, test.trace, "[7]", nil)
	}
	failedWrite(dictionary+`note(2, alias)[note(3, [])] = note(1, 9)`,
		"unhashable type: list", "[1, 2, 3]", `{"b": 7, "a": 8}`, nil)
	fmt.Println("PASS first operand failure, deferred write checks, and preserved effects")

	frozenList := starlark.NewList([]starlark.Value{starlark.MakeInt(7)})
	frozenList.Freeze()
	const provided = "target = provided\nalias = target\n"
	failedWrite(provided+`note(2, alias)[note(3, 2)] = note(1, 9)`, "out of range", "[1, 2, 3]", "[7]",
		starlark.StringDict{"provided": frozenList})
	failedWrite(provided+`note(2, alias)[note(3, 0)] = note(1, 9)`, "frozen list", "[1, 2, 3]", "[7]",
		starlark.StringDict{"provided": frozenList})
	frozenDict := starlark.NewDict(1)
	require(frozenDict.SetKey(starlark.String("b"), starlark.MakeInt(7)) == nil, "setting fixture key")
	frozenDict.Freeze()
	failedWrite(provided+`note(2, alias)[note(3, [])] = note(1, 9)`, "frozen hash table", "[1, 2, 3]", `{"b": 7}`,
		starlark.StringDict{"provided": frozenDict})
	fmt.Println("PASS list bounds precede freezing, and dictionary freezing precedes hashing")

	const loop = "def visit():\n    for item in target:\n        "
	activeList := failedWrite(list+loop+"note(2, alias)[note(3, 0)] = note(1, 9)\nvisit()",
		"during iteration", "[1, 2, 3]", "[7]", nil).(*starlark.List)
	activeDict := failedWrite(dictionary+loop+"note(2, alias)[note(3, [])] = note(1, 9)\nvisit()",
		"during iteration", "[1, 2, 3]", `{"b": 7, "a": 8}`, nil).(*starlark.Dict)
	require(activeList.Append(starlark.None) == nil && activeDict.SetKey(starlark.String("c"), starlark.None) == nil,
		"failed iteration should release its guards")
	fmt.Println("PASS alias mutation guards and cleanup on loop failure")
}
