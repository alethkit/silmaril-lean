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

	g, err = run(list+`def grow():
    events.append(3)
    alias.append(77)
    return -1
note(1, alias)[note(2, -1)] += grow()`, nil)
	require(err == nil && g["events"].String() == "[1, 2, 3]" && g["target"].String() == "[7, 6]" &&
		g["target"] == g["alias"], fmt.Sprint(err))
	g, err = run(dictionary+`note(1, alias)[note(2, "b")] += note(3, 9)`, nil)
	require(err == nil && g["events"].String() == "[1, 2, 3]" &&
		g["target"].String() == `{"b": 16, "a": 8}` && g["target"] == g["alias"], fmt.Sprint(err))
	g, err = run(`first = [7]
second = [50]
selected = [first]
def choose():
    return selected[0]
def change():
    selected[0] = second
    first[0] = 100
    return 2
def update():
    choose()[0] += change()
update()
first[0] += 1`, nil)
	require(err == nil && g["first"].String() == "[10]" && g["second"].String() == "[50]" &&
		g["selected"].(*starlark.List).Index(0) == g["second"], fmt.Sprint(err))
	fmt.Println("PASS augmented receiver and index evaluated once, old value read before RHS, saved raw index and identity used for write")

	for _, test := range []struct{ stmt, trace, message string }{
		{`len(note(1, 9))[note(2, 0)] += note(3, 9)`, "[1]", "has no len"},
		{`note(1, alias)[len(note(2, 9))] += note(3, 9)`, "[1, 2]", "has no len"},
		{`note(1, alias)[note(2, 0)] += len(note(3, 9))`, "[1, 2, 3]", "has no len"},
		{`note(1, alias)[note(2, 2)] += note(3, 9)`, "[1, 2]", "out of range"},
	} {
		failedWrite(list+test.stmt, test.message, test.trace, "[7]", nil)
	}
	failedWrite(provided+`note(1, alias)[note(2, "absent")] += note(3, 9)`,
		"key \"absent\" not in dict", "[1, 2]", `{"b": 7}`, starlark.StringDict{"provided": frozenDict})
	failedWrite(provided+`note(1, alias)[note(2, [])] += note(3, 9)`,
		"unhashable type: list", "[1, 2]", `{"b": 7}`, starlark.StringDict{"provided": frozenDict})
	failedWrite(list+`def fail_rhs():
    alias[0] = 100
    return len(note(3, 9))
note(1, target)[note(2, 0)] += fail_rhs()`, "has no len", "[1, 2, 3]", "[100]", nil)
	failedWrite(provided+`note(1, alias)[note(2, 0)] += note(3, True)`,
		"unknown binary op: int + bool", "[1, 2, 3]", "[7]", starlark.StringDict{"provided": frozenList})
	failedWrite(provided+`note(1, alias)[note(2, 0)] += note(3, 9)`,
		"frozen list", "[1, 2, 3]", "[7]", starlark.StringDict{"provided": frozenList})
	augmentedActiveDict := failedWrite(dictionary+loop+"note(1, alias)[note(2, \"b\")] += note(3, 9)\nvisit()",
		"during iteration", "[1, 2, 3]", `{"b": 7, "a": 8}`, nil).(*starlark.Dict)
	require(augmentedActiveDict.SetKey(starlark.String("c"), starlark.None) == nil,
		"failed augmented assignment should release the iterator guard")
	fmt.Println("PASS augmented read, RHS, operator and write failure order, preserved effects, and iterator cleanup")
}
