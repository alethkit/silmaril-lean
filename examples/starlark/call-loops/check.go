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

	const prepare = `def prepare(xs):
    xs.append(3)
    return xs
xs = [1, 2]
seen = []
`
	g, err = initSource(prepare + `def visit():
    for x in prepare(xs):
        seen.append(x)
visit()`)
	require(err == nil && g["xs"].String() == "[1, 2, 3]" && g["seen"].String() == "[1, 2, 3]",
		fmt.Sprint(err))
	fmt.Println("PASS the iterable call runs once and its mutation enters the snapshot")

	g, err = initSource(prepare + `def visit():
    for x in len(prepare(xs) and 9):
        seen.append(x)
visit()`)
	require(err != nil && strings.Contains(err.Error(), "has no len"), fmt.Sprint(err))
	xs = g["xs"].(*starlark.List)
	require(xs.String() == "[1, 2, 3]" && g["seen"].String() == "[]" && xs.Append(starlark.MakeInt(4)) == nil,
		"an operand error must retain its mutation without leaving an iterator or running the loop body")
	fmt.Println("PASS an iterable operand error keeps its effects before iterator acquisition")

	g, err = initSource(prepare + `def visit():
    alias = xs
    for x in prepare(xs):
        alias.append(4)
visit()`)
	require(err != nil && strings.Contains(err.Error(), "during iteration"), fmt.Sprint(err))
	xs = g["xs"].(*starlark.List)
	require(xs.String() == "[1, 2, 3]" && xs.Append(starlark.MakeInt(4)) == nil,
		"the loop's guard must reject the alias write and then be released on failure")
	fmt.Println("PASS alias mutation is guarded after acquisition and the guard is released on error")

	g, err = initSource(`def prepare():
    calls.append(1)
    return range(10, 3, -2)
def visit():
    x = 7
    for x in range(0):
        seen.append(99)
    empty = x
    for x in prepare()[::-2]:
        seen.append(x)
        continue
        seen.append(99)
    return (empty, x)
def early_break():
    for x in range(11, 1000000011):
        break
    return x
def early_return():
    for x in range(11, 1000000011):
        return x
calls = []
seen = []
out = visit()
early = (early_break(), early_return())`)
	require(err == nil, fmt.Sprint(err))
	require(g["calls"].String() == "[1]" && g["seen"].String() == "[4, 8]" &&
		g["out"].String() == "(7, 8)" && g["early"].String() == "(11, 11)",
		"range order, operand effects, binder updates, or early exit differed")
	fmt.Println("PASS empty and sliced descending ranges, single operand evaluation, continue and huge early exits")

	g, err = initSource(`def prepare():
    calls.append(1)
    return range(10, 3, -2)
def visit():
    for x in prepare()[::0]:
        seen.append(x)
calls = []
seen = []
visit()`)
	require(err != nil && strings.Contains(err.Error(), "zero is not a valid slice step"), fmt.Sprint(err))
	require(g["calls"].String() == "[1]" && g["seen"].String() == "[]",
		"a failing range slice must retain its operand effect and skip the body")
	fmt.Println("PASS a failing range operand keeps its effects before acquisition")

	g, err = initSource(`def visit():
    alias = xs
    for y in xs:
        for x in range(10, 3, -2):
            seen.append(x)
            alias.append(y)
xs = [1, 2]
seen = []
visit()`)
	require(err != nil && strings.Contains(err.Error(), "during iteration"), fmt.Sprint(err))
	xs = g["xs"].(*starlark.List)
	require(xs.String() == "[1, 2]" && g["seen"].String() == "[10]" && xs.Append(starlark.MakeInt(99)) == nil,
		"a nested range error must retain its effects and release the enclosing list guard")
	fmt.Println("PASS a range body failure keeps preceding effects and releases the enclosing list guard")
}
