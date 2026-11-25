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
	checkComprehensionStores()
	checkComprehensionAugmentedStores()
}

func brokenOperand(marker int) string {
	return fmt.Sprintf("[[][0] for row in note(%d, rows) for x in row]", marker)
}

func checkOperandGuards(g starlark.StringDict) {
	outer := g["rows"].(*starlark.List)
	inner := outer.Index(0).(*starlark.List)
	require(outer.Append(starlark.None) == nil && inner.Append(starlark.None) == nil,
		"failed operand left a comprehension guard active")
}

func checkComprehensionStores() {
	const sameAliasReceiver = "[note(2, alias) for x in alias][0]"
	const receiver = "[x for x in [note(2, alias)]][0]"
	const index = "[x for x in [note(3, 0)]][0]"
	const rhs = "[x for x in [note(1, 9)]][0]"
	g, err := run(list+`def change():
    [note(2, alias) for x in alias][0][[x for x in [note(3, -1)]][0]] = [x for x in [note(1, 9)]][0]
change()
table = {"b": 7, "a": 8}
twin = table
def choose():
    table["c"] = 11
    return note(6, "b")
[x for x in [note(5, twin)]][0][{x: choose() for x in [0]}[0]] = [x for x in [note(4, 10)]][0]
twin[[x for x in ["d"]][0]] = 12
`, nil)
	require(err == nil && g["events"].String() == "[1, 2, 3, 4, 5, 6]" && g["target"].String() == "[9]" &&
		g["target"] == g["alias"] && g["table"] == g["twin"] &&
		g["table"].String() == `{"b": 10, "a": 8, "c": 11, "d": 12}`, fmt.Sprint(g, err))
	fmt.Println("PASS each store operand runs once, aliased list and dictionary writes see the final heap")

	const invalid = "[x for x in [note(2, 7)]][0]"
	for _, tc := range []struct {
		receiver, index, rhs, message, trace string
	}{
		{receiver, index, brokenOperand(1), "out of range", "[1]"},
		{brokenOperand(2), index, rhs, "out of range", "[1, 2]"},
		{invalid, brokenOperand(3), rhs, "out of range", "[1, 2, 3]"},
		{invalid, index, rhs, "does not support item assignment", "[1, 2, 3]"},
	} {
		body := fmt.Sprintf("%srows = [[0]]\n(%s)[%s] = %s\nnote(99, 0)", list, tc.receiver, tc.index, tc.rhs)
		g, err = run(body, nil)
		require(err != nil && strings.Contains(err.Error(), tc.message), fmt.Sprint(err))
		require(g["events"].String() == tc.trace && g["target"].String() == "[7]" &&
			g["target"] == g["alias"], fmt.Sprint(g, err))
		checkOperandGuards(g)
	}
	fmt.Println("PASS comprehension operand errors short-circuit and precede target validation")

	const badKey = "[x for x in [note(3, [])]][0]"
	const oldDict = `{"b": 7, "a": 8}`
	failedWrite(dictionary+receiver+"["+badKey+"] = "+rhs, "unhashable type: list", "[1, 2, 3]", oldDict, nil)
	const provided = "target = provided\nalias = target\n"
	frozenList := starlark.NewList([]starlark.Value{starlark.MakeInt(7)})
	frozenList.Freeze()
	failedWrite(provided+receiver+"[[x for x in [note(3, 2)]][0]] = "+rhs, "out of range", "[1, 2, 3]", "[7]",
		starlark.StringDict{"provided": frozenList})
	frozenDict := starlark.NewDict(1)
	require(frozenDict.SetKey(starlark.String("b"), starlark.MakeInt(7)) == nil, "setting fixture key")
	frozenDict.Freeze()
	failedWrite(provided+receiver+"["+badKey+"] = "+rhs, "frozen hash table", "[1, 2, 3]", `{"b": 7}`,
		starlark.StringDict{"provided": frozenDict})

	active := failedWrite(list+"def visit():\n    for x in target:\n        "+
		sameAliasReceiver+"["+index+"] = "+rhs+"\nvisit()", "during iteration", "[1, 2, 3]", "[7]", nil)
	require(active.(*starlark.List).Append(starlark.None) == nil, "failed store left its enclosing iterator active")
	fmt.Println("PASS saved operands retain list bounds, dictionary hashing, freezing, and same-alias guard order")
}

func checkComprehensionAugmentedStores() {
	g, err := run(`first = [7]
second = [50]
alias = first
selected = [alias]
def change():
    selected[0] = second
    alias[0] = 100
    return note(3, 2)
def update():
    [x for x in [note(1, selected[0])]][0][[x for x in [note(2, -1)]][0]] += [x for x in [change()]][0]
update()
table = {"b": 7, "a": 8}
twin = table
[x for x in [note(4, twin)]][0][[x for x in [note(5, "b")]][0]] += [x for x in [note(6, 9)]][0]
def bump(x):
    x += [x for x in [note(7, x)]][0]
    return x
out = bump(3)
`, nil)
	require(err == nil && g["events"].String() == "[1, 2, 3, 4, 5, 6, 7]" && g["first"] == g["alias"] &&
		g["first"].String() == "[9]" && g["second"].String() == "[50]" && g["selected"].String() == "[[50]]" &&
		g["table"] == g["twin"] && g["table"].String() == `{"b": 16, "a": 8}` && g["out"].String() == "6",
		fmt.Sprint(g, err))
	fmt.Println("PASS augmented comprehension operands run once and retain old value and receiver identity")

	const receiver = "[x for x in [note(1, alias)]][0]"
	const index = "[x for x in [note(2, 0)]][0]"
	const rhs = "[x for x in [note(3, 9)]][0]"
	const absent = "[x for x in [note(2, \"new\")]][0]"
	const oldDict = `{"b": 7, "a": 8}`
	g, err = run(list+`def grow():
    alias.append(77)
    return note(3, -1)
`+receiver+"[[x for x in [note(2, -1)]][0]] += [x for x in [grow()]][0]", nil)
	require(err == nil && g["events"].String() == "[1, 2, 3]" && g["target"].String() == "[7, 6]" &&
		g["target"] == g["alias"], fmt.Sprint(g, err))
	fmt.Println("PASS augmented write normalizes the saved negative index after RHS growth")

	g, err = run(dictionary+receiver+"["+absent+"] = "+rhs, nil)
	require(err == nil && g["events"].String() == "[3, 1, 2]" && g["target"].String() == `{"b": 7, "a": 8, "new": 9}`,
		fmt.Sprint(g, err))
	failedWrite(dictionary+receiver+"["+absent+"] += "+rhs, "key \"new\" not in dict", "[1, 2]", oldDict, nil)
	fmt.Println("PASS plain store runs RHS first and inserts a key, augmented read fails before RHS")

	for _, tc := range []struct {
		receiver, index, rhs, trace string
	}{
		{brokenOperand(1), index, rhs, "[1]"},
		{receiver, brokenOperand(2), rhs, "[1, 2]"},
		{receiver, "[x for x in [note(2, 2)]][0]", rhs, "[1, 2]"},
		{receiver, index, brokenOperand(3), "[1, 2, 3]"},
	} {
		body := fmt.Sprintf("%srows = [[0]]\n(%s)[%s] += %s\nnote(99, 0)", list, tc.receiver, tc.index, tc.rhs)
		g, err = run(body, nil)
		require(err != nil && strings.Contains(err.Error(), "out of range"), fmt.Sprint(g, err))
		require(g["events"].String() == tc.trace && g["target"].String() == "[7]" && g["target"] == g["alias"],
			fmt.Sprint(g, err))
		checkOperandGuards(g)
	}
	g, err = run(list+`rows = [[0]]
def change():
    alias[0] = 100
    return note(3, rows)
`+receiver+"["+index+"] += [[][0] for row in change() for x in row]\nnote(99, 0)", nil)
	require(err != nil && strings.Contains(err.Error(), "out of range"), fmt.Sprint(g, err))
	require(g["events"].String() == "[1, 2, 3]" && g["target"].String() == "[100]" && g["target"] == g["alias"],
		fmt.Sprint(g, err))
	checkOperandGuards(g)
	fmt.Println("PASS early and late operand failures unwind comprehension guards and retain earlier alias effects")

	const provided = "target = provided\nalias = target\n"
	frozen := starlark.NewList([]starlark.Value{starlark.MakeInt(7)})
	frozen.Freeze()
	providedEnv := starlark.StringDict{"provided": frozen}
	failedWrite(provided+receiver+"["+index+"] += [x for x in [note(3, True)]][0]",
		"unknown binary op: int + bool", "[1, 2, 3]", "[7]", providedEnv)
	failedWrite(provided+receiver+"["+index+"] += "+rhs, "frozen list", "[1, 2, 3]", "[7]", providedEnv)
	active := failedWrite(list+"def visit():\n    for x in target:\n        "+
		"[note(1, alias) for y in alias][0]["+index+"] += "+rhs+"\nvisit()",
		"during iteration", "[1, 2, 3]", "[7]", nil)
	require(active.(*starlark.List).Append(starlark.None) == nil, "failed augmented store left an iterator guard active")

	g, err = run("x = 7\ndef f():\n    x += "+rhs+"\nf()", nil)
	require(err != nil && strings.Contains(err.Error(), "local variable x referenced before assignment") &&
		g["events"].String() == "[]", fmt.Sprint(g, err))
	fmt.Println("PASS arithmetic precedes final guards and an unbound name skips its RHS")
}
