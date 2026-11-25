// Run from the pinned starlark-go checkout with default file options.
package main

import (
	"fmt"
	"strings"

	"go.starlark.net/starlark"
	"go.starlark.net/syntax"
)

func run(source string) (starlark.StringDict, error) {
	_, program, err := starlark.SourceProgramOptions(
		&syntax.FileOptions{}, "comprehensions.star", source+"\n", func(string) bool { return false },
	)
	if err != nil {
		return nil, err
	}
	return program.Init(&starlark.Thread{Name: "comprehensions"}, nil)
}

func require(ok bool, context string) {
	if !ok {
		panic(context)
	}
}

func checkError(err error, text string) {
	require(err != nil && strings.Contains(err.Error(), text), fmt.Sprintf("want %q, got %v", text, err))
}

func checkLists() {
	globals, err := run(`def run(x):
    result = [(x, z) for (x, [x, y]) in x if x for [z, (w, z)] in y if w]
    return (len(x), result)
out = run([(10, [0, 19]), (20, [3, [(5, (0, 9)), (6, (1, 8))]])])
`)
	require(err == nil && globals["out"].String() == "(2, [(3, 8)])", fmt.Sprint(globals, err))
	_, err = run(`z = [8]
out = [x for x in [1] for y in z for z in []]`)
	checkError(err, "referenced before assignment")
	_, err = run(`out = [y for (x, [y]) in []]
read = y`)
	checkError(err, "undefined: y")
	_, err = run(`out = [x for x in [] for (x, [y, 3]) in []]`)
	checkError(err, "can't assign")
	fmt.Println("PASS enclosing operand, repeated leaves, filters, later generator, and lexical isolation")

	globals, err = run(`rows = [[[1, [2, 3]], [5, [6]]]]
effects = [0, 0]
def start():
    effects[0] += 1
    return rows
def observe(x):
    effects[1] = x
    return x
out = [observe(a) for row in start() if row for (a, [b, c]) in row]`)
	checkError(err, "too few values to unpack")
	require(globals["out"] == nil && globals["effects"].String() == "[1, 1]", fmt.Sprint(globals))
	outer := globals["rows"].(*starlark.List)
	inner := outer.Index(0).(*starlark.List)
	require(outer.Append(starlark.None) == nil && inner.Append(starlark.None) == nil,
		"iterator guard survived failed initialization")
	fmt.Println("PASS operand evaluated once, prior yield effects retained, both guards released after mismatch")

	globals, err = run(`out = [y for x in [1, 0] if x or y for y in [2]]`)
	require(err == nil && globals["out"].String() == "[2, 2]", fmt.Sprint(globals, err))

	globals, err = run(`def run():
    results = []
    for source in [[1], [0]]:
        results.append([y for x in source if x or y for y in [2]])
    return results
out = run()`)
	require(err == nil && globals["out"].String() == "[[2], [2]]", fmt.Sprint(globals, err))
	fmt.Println("PROFILE DIFFERENCE Go retains comprehension locals across visits to the same site")
}

func checkDictionaries() {
	globals, err := run(`def run(x):
    result = {k: (x, v) for (x, [x, ys]) in x if x for [k, [v]] in ys}
    return (len(x), result["a"])
out = run([(8, [0, 9]), (9, [7, [("a", [4])]])])
`)
	require(err == nil && globals["out"].String() == "(2, (7, 4))", fmt.Sprint(globals, err))
	_, err = run(`out = {x: y for (x, [y]) in []}
read = y`)
	checkError(err, "undefined: y")

	const mark = `events = []
def mark(tag, value):
    events.append(tag)
    return value
`
	const clauses = ` for row in mark(9, rows) for (k, [v]) in row if v}`
	globals, err = run(mark + `rows = [[("a", [1]), ("b", [2]), ("a", [3]), ("c", [0])]]
out = {mark(1, k): mark(2, v)` + clauses)
	require(err == nil && globals["out"].String() == `{"a": 3, "b": 2}` &&
		globals["events"].String() == "[9, 1, 2, 1, 2, 1, 2]", fmt.Sprint(globals, err))
	fmt.Println("PASS dictionary scope, outer operand evaluated once, filters, ordered effects, and overwrite in insertion order")

	const badRows = `rows = [[("a", [1]), ([], [2]), ("b", [3])]]
`
	for _, tc := range []struct {
		pair      string
		errorPart string
		events    string
	}{
		{`(mark(1, k) if k else mark(1, k)[1]): mark(2, v)`, "out of range", "[9, 1, 2, 1]"},
		{`mark(1, k): (mark(2, v) if k else mark(2, v)[0])`, "unhandled index operation", "[9, 1, 2, 1, 2]"},
		{`mark(1, k): mark(2, v)`, "unhashable type: list", "[9, 1, 2, 1, 2]"},
	} {
		globals, err = run(mark + badRows + "out = {" + tc.pair + clauses)
		checkError(err, tc.errorPart)
		require(globals["out"] == nil && globals["events"].String() == tc.events, fmt.Sprint(globals, err))
		outer := globals["rows"].(*starlark.List)
		inner := outer.Index(0).(*starlark.List)
		require(outer.Append(starlark.None) == nil && inner.Append(starlark.None) == nil,
			"dictionary comprehension left an active iterator after failure")
	}
	fmt.Println("PASS key/value/hash failure precedence, residual effects, and both guard releases")

	globals, err = run(`def run():
    results = []
    for source in [[1], [0]]:
        results.append({y: x for x in source if x or y for y in [2]})
    return results
out = run()`)
	require(err == nil && globals["out"].String() == "[{2: 1}, {2: 0}]", fmt.Sprint(globals, err))
	fmt.Println("PROFILE DIFFERENCE Go also retains dictionary comprehension locals across visits")
}

func checkExpressionPositions() {
	const mark = `events = []
def mark(tag, value):
    events.append(tag)
    return value
`
	globals, err := run(mark + `def sink(xs, d, last):
    return mark(9, (xs[0], d["a"], last))
def pick():
    return mark(1, sink)
def run():
    return pick()(
        [mark(3, x) for x in mark(2, [4])] or [x for x in mark(99, len(1))],
        {mark(5, k): mark(6, v) for (k, [v]) in mark(4, [("a", [10])])} if True else [x for x in mark(99, len(1))],
        len(mark(8, range(11))),
    )
out = run()
`)
	require(err == nil && globals["out"].String() == "(4, 10, 11)" &&
		globals["events"].String() == "[1, 2, 3, 4, 5, 6, 8, 9]", fmt.Sprint(globals, err))
	fmt.Println("PASS comprehension arguments inside a return, callee/argument order, and skipped branches")

	const calls = `rows = [[("a", [4]), ([], [5])]]
def sink(*args):
    return mark(7, args)
`
	const arguments = `(
    [x for x in mark(2, [])],
    {mark(4, k): mark(5, v) for row in mark(3, rows) for (k, [v]) in row},
    mark(6, 0),
)
`
	for _, tc := range []struct {
		callee    string
		errorPart string
		events    string
	}{
		{`mark(1, sink)`, "unhashable type: list", "[1, 2, 3, 4, 5, 4, 5]"},
		{`mark(1, [])[1]`, "out of range", "[1]"},
	} {
		globals, err = run(mark + calls + "out = " + tc.callee + arguments)
		checkError(err, tc.errorPart)
		require(globals["out"] == nil && globals["events"].String() == tc.events, fmt.Sprint(globals, err))
		outer := globals["rows"].(*starlark.List)
		inner := outer.Index(0).(*starlark.List)
		require(outer.Append(starlark.None) == nil && inner.Append(starlark.None) == nil,
			"expression-position failure left an active iterator")
	}
	fmt.Println("PASS failed callee or comprehension skips later arguments and dispatch, retaining effects")
}

func checkCallOperands() {
	const mark = `events = []
def mark(tag, value):
    events.append(tag)
    return value
`
	const callee = `(sink if [mark(2, x) for x in mark(1, [True])] else len(1))`
	globals, err := run(mark + `def sink(a, b, k, z):
    return mark(9, (a, b, k[0], z))
def run():
    return ` + callee + `(
        mark(3, 9),
        k=[mark(5, x) for x in mark(4, [10])],
        *[mark(7, x) for x in mark(6, [11])],
        **{n: v for (n, v) in mark(8, [("z", 12)])},
    )
out = run()
`)
	require(err == nil && globals["out"].String() == "(9, 11, 10, 12)" &&
		globals["events"].String() == "[1, 2, 3, 4, 5, 6, 7, 8, 9]", fmt.Sprint(globals, err))

	globals, err = run(`xs = [1]
def bump(value):
    xs[0] = 9
    return value
def sink(a, b):
    return (a, b)
out = sink(*xs, **{k: bump(v) for (k, v) in [("b", 2)]})
`)
	require(err == nil && globals["out"].String() == "(9, 2)", fmt.Sprint(globals, err))
	fmt.Println("PASS comprehension callee, keyword and spreads, including mutation before expansion")

	const prelude = `rows = [[("a", [4]), ([], [5])]]
def sink(*rest, k=0):
    return mark(7, k)
`
	const named = `k=[x for x in mark(3, [5])]`
	const goodStar = `*[x for x in mark(4, [6])]`
	const badStar = `*mark(4, 0)`
	const duplicate = `**{k: mark(6, v) for (k, v) in mark(5, [("k", 8)])}`
	const nonString = `**{k: mark(6, v) for (k, v) in mark(5, [(1, 8)])}`
	const badMapping = `**[x for x in mark(5, [])]`
	const failed = `{mark(4, k): mark(5, v) for row in mark(3, rows) for (k, [v]) in row}`
	for _, tc := range []struct {
		callee    string
		arguments string
		errorPart string
		events    string
	}{
		{callee, named + ", " + goodStar + ", " + duplicate, `multiple values for parameter "k"`, "[1, 2, 3, 4, 5, 6]"},
		{callee, named + ", " + badStar + ", " + nonString, "keywords must be strings", "[1, 2, 3, 4, 5, 6]"},
		{callee, named + ", " + badStar + ", " + badMapping, "argument after ** must be a mapping", "[1, 2, 3, 4, 5]"},
		{callee, named + ", " + badStar + ", " + duplicate, "argument after * must be iterable", "[1, 2, 3, 4, 5, 6]"},
		{callee, badStar + ", **" + failed, "unhashable type: list", "[1, 2, 4, 3, 4, 5, 4, 5]"},
		{"(sink if " + failed + " else sink)", named + ", " + goodStar + ", " + duplicate,
			"unhashable type: list", "[3, 4, 5, 4, 5]"},
	} {
		globals, err = run(mark + prelude + "out = " + tc.callee + "(" + tc.arguments + ")")
		checkError(err, tc.errorPart)
		require(globals["out"] == nil && globals["events"].String() == tc.events, fmt.Sprint(globals, err))
		outer := globals["rows"].(*starlark.List)
		inner := outer.Index(0).(*starlark.List)
		require(outer.Append(starlark.None) == nil && inner.Append(starlark.None) == nil,
			"failed callee or expansion operand left an iterator active")
	}
	_, err = run(`out = len(x=[x for x in []], x=[y for y in []]) if False else None`)
	checkError(err, `keyword argument "x" is repeated`)
	fmt.Println("PASS operand versus expansion versus binding errors, duplicate keyword checks, and iterator cleanup")
}

func main() {
	checkLists()
	checkDictionaries()
	checkExpressionPositions()
	checkCallOperands()
}
