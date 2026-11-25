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

func collectionOperands() {
	const setup = `def note(marker, value):
    events.append(marker)
    return value
events = []
`
	g, err := initSource(setup + `out = [note(1, 17), note(2, 22),][note(3, -1)]`)
	require(err == nil && g["out"].String() == "22" && g["events"].String() == "[1, 2, 3]", fmt.Sprint(err))
	fmt.Println("PASS list elements, receiver and subscript evaluate once in order")

	g, err = initSource(setup + `out = note(1, events)[note(2, -1)]`)
	require(err == nil && g["out"].String() == "2" && g["events"].String() == "[1, 2]", fmt.Sprint(err))
	fmt.Println("PASS the subscript observes a receiver mutation performed by the index operand")

	for _, test := range []struct{ expr, trace, message string }{
		{`[note(1, 17), len(note(2, 9)), note(3, 22)]`, "[1, 2]", "has no len"},
		{`len(note(1, 9))[note(2, 0)]`, "[1]", "has no len"},
		{`[note(1, 17)][len(note(2, 9))]`, "[1, 2]", "has no len"},
		{`note(1, 17)[note(2, 0)]`, "[1, 2]", "unhandled index operation"},
	} {
		g, err := initSource(setup + "out = " + test.expr)
		require(err != nil && strings.Contains(err.Error(), test.message), fmt.Sprint(err))
		require(g["out"] == nil && g["events"].String() == test.trace, test.expr)
	}
	fmt.Println("PASS list and subscript failures retain exactly the earlier effects")

	g, err = initSource(setup + `out = (note(1, 17), note(2, 22),)[note(3, -1)]`)
	require(err == nil && g["out"].String() == "22" && g["events"].String() == "[1, 2, 3]", fmt.Sprint(err))
	g, err = initSource(setup + `out = (note(1, 17), len(note(2, 9)), note(3, 22))`)
	require(err != nil && strings.Contains(err.Error(), "has no len") && g["out"] == nil &&
		g["events"].String() == "[1, 2]", fmt.Sprint(err))
	fmt.Println("PASS tuple elements evaluate once in order and stop at the first error")

	const pairs = `note(1, "b"): note(2, 17), note(3, "a"): note(4, 22)`
	g, err = initSource(setup + "out = {" + pairs + "}")
	require(err == nil && g["out"].String() == `{"b": 17, "a": 22}` &&
		g["events"].String() == "[1, 2, 3, 4]", fmt.Sprint(err))
	fmt.Println("PASS dictionary key/value effects and insertion order")

	for _, test := range []struct{ expr, trace, message string }{
		{`{` + pairs + `, note(5, "b"): note(6, 33), note(7, "later"): note(8, 9)}`, "[1, 2, 3, 4, 5, 6]", "duplicate key"},
		{`{` + pairs + `, note(5, []): note(6, 9), note(7, "later"): note(8, 9)}`, "[1, 2, 3, 4, 5, 6]", "unhashable type: list"},
		{`{len(note(1, 9)): note(2, 17)}`, "[1]", "has no len"},
		{`{note(1, []): len(note(2, 9))}`, "[1, 2]", "has no len"},
	} {
		g, err := initSource(setup + "out = " + test.expr)
		require(err != nil && strings.Contains(err.Error(), test.message), fmt.Sprint(err))
		require(g["out"] == nil && g["events"].String() == test.trace, test.expr)
	}
	fmt.Println("PASS dictionary operands and insertion stop at the first failure, including duplicate and hash errors")

	frozen := starlark.NewList(nil)
	frozen.Freeze()
	_, err = frozen.Hash()
	require(err != nil && strings.Contains(err.Error(), "unhashable type: list"), fmt.Sprint(err))
	fmt.Println("DIALECT pinned Go rejects frozen list keys")
}

func sliceOperands() {
	const setup = `def note(marker, value):
    events.append(marker)
    return value
events = []
`
	g, err := initSource(setup + `out = note(1, events)[note(2, None):note(3, None):note(4, -2)]`)
	require(err == nil && g["out"].String() == "[4, 2]" && g["events"].String() == "[1, 2, 3, 4]" &&
		g["out"] != g["events"], fmt.Sprint(err))
	fmt.Println("PASS slice operands run once, in source order, before taking the slice of the mutated receiver")

	for _, test := range []struct{ expr, want string }{
		{`[0, 1, 2, 3, 4][:]`, "[0, 1, 2, 3, 4]"},
		{`[0, 1, 2, 3, 4][-4:-1:2]`, "[1, 3]"},
		{`[0, 1, 2, 3, 4][100:-100:-2]`, "[4, 2, 0]"},
		{`(0, 1, 2, 3, 4)[::-2]`, "(4, 2, 0)"},
		{`(0, 1, 2, 3, 4)[None:None:None]`, "(0, 1, 2, 3, 4)"},
		{`(0, 1, 2, 3, 4)[:-1:-1]`, "()"},
		{`[0, 1, 2, 3, 4][-100::-1]`, "[]"},
		{`[][::-1]`, "[]"},
	} {
		g, err := initSource("out = " + test.expr)
		require(err == nil && g["out"].String() == test.want, test.expr+": "+fmt.Sprint(err))
	}
	fmt.Println("PASS omitted and None bounds, negative bounds and stride, and empty results")

	for _, test := range []struct{ expr, trace, message string }{
		{`len(note(1, 9))[note(2, None):note(3, None):note(4, 1)]`, "[1]", "has no len"},
		{`note(1, events)[len(note(2, 9)):note(3, None):note(4, 1)]`, "[1, 2]", "has no len"},
		{`note(1, 42)[note(2, True):len(note(3, 9)):note(4, 0)]`, "[1, 2, 3]", "has no len"},
		{`note(1, events)[note(2, True):note(3, True):len(note(4, 9))]`, "[1, 2, 3, 4]", "has no len"},
		{`note(1, 42)[note(2, True):note(3, True):note(4, 0)]`, "[1, 2, 3, 4]", "invalid slice operand"},
		{`note(1, events)[note(2, True):note(3, True):note(4, True)]`, "[1, 2, 3, 4]", "invalid slice step"},
		{`note(1, events)[note(2, True):note(3, True):note(4, 0)]`, "[1, 2, 3, 4]", "zero is not a valid slice step"},
		{`note(1, events)[note(2, True):note(3, True):note(4, None)]`, "[1, 2, 3, 4]", "invalid start index"},
		{`note(1, events)[note(2, None):note(3, True):note(4, -1)]`, "[1, 2, 3, 4]", "invalid end index"},
	} {
		g, err := initSource(setup + "out = " + test.expr + "\nnote(99, None)")
		require(err != nil && strings.Contains(err.Error(), test.message), test.expr+": "+fmt.Sprint(err))
		require(g["out"] == nil && g["events"].String() == test.trace, test.expr)
	}
	fmt.Println("PASS a failed operand skips the rest, and validation checks receiver, stride, start and stop")

	g, err = initSource(`def pick(value):
    return value
inner = [7]
items = [inner, [8]]
def driver():
    return pick(items)[pick(None)::pick(-1)]
out = driver()
inner[0] = 42
out[0] = None
shared = out[1][0]
untouched = items[1][0]
tupleKey = {(0, 1, 2)[pick(1):] : 9}[(1, 2)]
`)
	require(err == nil && g["out"] != g["items"] && g["out"].(*starlark.List).Index(1) == g["inner"] &&
		g["shared"].String() == "42" && g["untouched"].String() == "8" && g["tupleKey"].String() == "9", fmt.Sprint(err))
	fmt.Println("PASS list slices are shallow copies and sliced tuples remain usable as dictionary keys")

	_, err = initSource(`out = [0, 1, 2][-100000000000:100000000000:100000000000]`)
	require(err != nil && strings.Contains(err.Error(), "invalid slice step"), fmt.Sprint(err))
	fmt.Println("DIALECT pinned Go rejects a stride outside signed 32 bits")

	g, err = initSource(setup + `out = note(1, "aé🙂z")[note(2, 1):note(3, -1):note(4, None)]
size = len(out)
reverse = "aéz"[::-3]
empty = "é"[1:1]`)
	require(err == nil && g["out"] == starlark.String("é🙂") && g["size"].String() == "6" &&
		g["reverse"] == starlark.String("za") && g["empty"] == starlark.String("") &&
		g["events"].String() == "[1, 2, 3, 4]", fmt.Sprint(err))
	fmt.Println("PASS string slices count UTF-8 bytes, including a valid reverse stride and an empty result")

	g, err = initSource(setup + `out = note(1, "aé🙂z")[note(2, 1):note(3, 2):note(4, None)]
reverse = "é"[::-1]
index = "é"[0]`)
	require(err == nil && g["out"] == starlark.String("\xc3") && g["reverse"] == starlark.String("\xa9\xc3") &&
		g["index"] == starlark.String("\xc3") && g["events"].String() == "[1, 2, 3, 4]", fmt.Sprint(err))
	fmt.Println("DIALECT pinned Go preserves malformed UTF-8 from a split, reversal or single-byte index")

	for _, test := range []struct{ expr, message string }{
		{`note(1, "é")[note(2, 0):note(3, 1):len(note(4, 9))]`, "has no len"},
		{`note(1, "é")[note(2, 0):note(3, 1):note(4, 0)]`, "zero is not a valid slice step"},
	} {
		g, err := initSource(setup + "out = " + test.expr)
		require(err != nil && strings.Contains(err.Error(), test.message), fmt.Sprint(err))
		require(g["out"] == nil && g["events"].String() == "[1, 2, 3, 4]", test.expr)
	}
	fmt.Println("PASS string slice operand and stride failures retain earlier effects")
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
out = len(events.append(1), ignored=len(events.append(2)), *events.append(3), **events.append(4))
`)
	require(err != nil && strings.Contains(err.Error(), "has no len"), fmt.Sprint(err))
	require(g["events"].String() == "[1, 2]" && g["out"] == nil,
		"the keyword expression's failure must skip both spreads and the destination write")
	fmt.Println("PASS a nested keyword operand failure skips the spread operands")

	g, err = initSource(`events = []
out = len(events.append(1), ignored=events.append(2), *events.append(3), **events.append(4))
`)
	require(err != nil && strings.Contains(err.Error(), "argument after ** must be a mapping"), fmt.Sprint(err))
	require(g["events"].String() == "[1, 2, 3, 4]" && g["out"] == nil,
		"all operand effects must survive the mapping error")
	fmt.Println("PASS all operands run before mapping validation, which precedes iterable validation")

	g, err = initSource(`events = []
out = len(*events.append(1), **{})
`)
	require(err != nil && strings.Contains(err.Error(), "argument after * must be iterable"), fmt.Sprint(err))
	require(g["events"].String() == "[1]" && g["out"] == nil,
		"the operand effect must survive the iterable error")
	fmt.Println("PASS a valid mapping exposes the iterable error")

	g, err = initSource(`def f(x):
    events.append("body")
events = []
out = f(x=events.append(1), **{"x": events.append(2)})
`)
	require(err != nil && strings.Contains(err.Error(), `multiple values for parameter "x"`), fmt.Sprint(err))
	require(g["events"].String() == "[1, 2]" && g["out"] == nil,
		"both effects must survive binding failure, without entering the function body")
	fmt.Println("PASS expansion reaches duplicate binding after both operands run")

	g, err = initSource(`events = []
out = events.append(1) and len(events.append(2))
`)
	require(err == nil && g["out"] == starlark.None && g["events"].String() == "[1]",
		"short-circuit must keep the left value and skip both the right effect and failure")
	fmt.Println("PASS skipped call leaves the first mutation and None result")

	g, err = initSource(`items = ("abc",)
keywords = {}
out = (len(*items, **keywords) or len(9)) if True else len(9)
`)
	require(err == nil && g["out"].String() == "3", fmt.Sprint(err))
	fmt.Println("PASS resolved built-in, global spreads and skipped calls agree with the Lean fixture")

	_, err = initSource(`out = 0 if True else missing
`)
	require(err != nil && strings.Contains(err.Error(), "undefined: missing"), fmt.Sprint(err))
	fmt.Println("PASS lexical resolution rejects an unknown name in an untaken branch")

	const mutatingBody = `def body(a, b, c, d):
    events.append(a)
    events.append(b)
    events.append(c)
    return len(d)
events = []
`
	g, err = initSource(mutatingBody + `out = body(1, c=3, *(2,), **{"d": events})`)
	require(err == nil && g["out"].String() == "3" && g["events"].String() == "[1, 2, 3]", fmt.Sprint(err))
	fmt.Println("PASS mixed operands invoke the closure and its inner built-in with a shared list")

	g, err = initSource(mutatingBody + `out = body(1, c=3, *(2,), **{"d": 9})`)
	require(err != nil && strings.Contains(err.Error(), "has no len"), fmt.Sprint(err))
	require(g["out"] == nil && g["events"].String() == "[1, 2, 3]", "callee effects must survive its error")
	fmt.Println("PASS callee effects survive failure in the inner built-in")

	const returnSetup = `def mark(n):
    events.append(n)
    return n
def pick(a, b, c):
    return (a, b, c)
events = []
`
	g, err = initSource(returnSetup + `def driver():
    return pick(mark(1), c=mark(2), *[events.append(3)])
out = driver()`)
	require(err == nil && g["out"].String() == "(1, None, 2)" && g["events"].String() == "[1, 2, 3]",
		fmt.Sprint(err))
	fmt.Println("PASS native return transfers the nested call value and its operand effects")

	g, err = initSource(returnSetup + `def driver():
    return pick(mark(1), c=len(mark(2)), *[events.append(3)])
out = driver()`)
	require(err != nil && strings.Contains(err.Error(), "has no len"), fmt.Sprint(err))
	require(g["out"] == nil && g["events"].String() == "[1, 2]", "return error must retain only earlier effects")
	fmt.Println("PASS native return retains prior effects and skips the spread after a nested keyword error")

	g, err = initSource(returnSetup + `def driver():
    out = 7
    out = len(mark(1))
    return out
out = driver()`)
	require(err != nil && strings.Contains(err.Error(), "has no len"), fmt.Sprint(err))
	require(g["out"] == nil && g["events"].String() == "[1]", "RHS failure must keep the nested call's effect")
	fmt.Println("PASS failed assignment keeps its RHS mutation and aborts result delivery")

	g, err = initSource(returnSetup + `def driver():
    if mark(1):
        out = mark(2)
    else:
        out = mark(3)
    return out
out = driver()`)
	require(err == nil && g["out"].String() == "2" && g["events"].String() == "[1, 2]", fmt.Sprint(err))
	fmt.Println("PASS an effectful condition runs once and only the chosen branch mutates")

	collectionOperands()
	sliceOperands()
}
