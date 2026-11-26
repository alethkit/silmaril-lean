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

func checkDisplayAndIndexOperands() {
	const mark = `events = []
def mark(tag, value):
    events.append(tag)
    return value
`
	globals, err := run(mark + `def example():
    return (
        [[x for x in mark(1, [7])], mark(2, 8)],
        {len([x for x in mark(3, [0])]): {k: v for (k, v) in mark(4, [("a", 9)])}},
        [x for x in mark(5, [10, 11])][len([x for x in mark(6, [0])])],
    )
out = example()
`)
	require(err == nil && globals["out"].String() == `([[7], 8], {1: {"a": 9}}, 11)` &&
		globals["events"].String() == "[1, 2, 3, 4, 5, 6]", fmt.Sprint(globals, err))
	fmt.Println("PASS nested comprehensions in list, tuple and dict displays and subscript operands")

	const rows = `rows = [[("a", [4]), ([], [5])]]
`
	const failed = `{mark(4, k): mark(5, v) for row in mark(3, rows) for (k, [v]) in row}`
	for _, tc := range []struct {
		expression string
		errorPart  string
		events     string
	}{
		{`[[x for x in mark(1, [7])], ` + failed + `, mark(2, 8)]`, "unhashable type: list", "[1, 3, 4, 5, 4, 5]"},
		{`([x for x in mark(1, [7])], ` + failed + `, mark(2, 8))`, "unhashable type: list", "[1, 3, 4, 5, 4, 5]"},
		{`{` + failed + `: [x for x in mark(1, [7])], mark(2, 0): 0}`, "unhashable type: list", "[3, 4, 5, 4, 5]"},
		{`{[x for x in mark(1, [])]: mark(2, [])[1], mark(3, 0): 0}`, "out of range", "[1, 2]"},
		{`{[x for x in mark(1, [])]: [y for y in mark(2, [9])], mark(3, 0): 0}`, "unhashable type: list", "[1, 2]"},
		{`{len([x for x in mark(1, [0])]): mark(2, 11), len([x for x in mark(3, [0])]): mark(4, 22), mark(5, 2): 0}`,
			"duplicate key", "[1, 2, 3, 4]"},
		{failed + `[len([x for x in mark(1, [0])])]`, "unhashable type: list", "[3, 4, 5, 4, 5]"},
		{`mark(1, 0)[mark(2, [])[1]]`, "out of range", "[1, 2]"},
		{`mark(1, 0)[[x for x in mark(2, [])]]`, "unhandled index operation", "[1, 2]"},
		{`[x for x in mark(1, [0])][[x for x in mark(2, [])]]`, "got list, want int", "[1, 2]"},
	} {
		globals, err = run(mark + rows + "out = " + tc.expression)
		checkError(err, tc.errorPart)
		require(globals["out"] == nil && globals["events"].String() == tc.events, fmt.Sprint(globals, err))
		outer := globals["rows"].(*starlark.List)
		inner := outer.Index(0).(*starlark.List)
		require(outer.Append(starlark.None) == nil && inner.Append(starlark.None) == nil,
			"failed display element or subscript operand left an iterator active")
	}
	fmt.Println("PASS display pair and indexing error precedence, residual effects, and iterator unwind")
}

func checkSliceOperands() {
	const mark = `events = []
def mark(tag, value):
    events.append(tag)
    return value
`
	globals, err := run(mark + `def example():
    return [x for x in mark(1, [0, 1, 2, 3, 4])][
        len([x for x in mark(2, [0, 0, 0, 0])]):
        len([x for x in mark(3, [])]):
        (-2 if [x for x in mark(4, [True])] else len(1))
    ]
out = example()
`)
	require(err == nil && globals["out"].String() == "[4, 2]" &&
		globals["events"].String() == "[1, 2, 3, 4]", fmt.Sprint(globals, err))

	globals, err = run(mark + `items = (
    [x for x in mark(1, [0, 1, 2])][::-1],
    (3, 4, 5)[len([x for x in mark(2, [0])]):],
    range(5)[:(None if [x for x in mark(3, [True])] else len(1)):-2],
    [x for x in mark(4, [0, 1, 2])][:-1:-1],
)
out = (items[0], items[1], list(items[2]), items[3])
`)
	require(err == nil && globals["out"].String() == "([2, 1, 0], (4, 5), [4, 2, 0], [])" &&
		globals["events"].String() == "[1, 2, 3, 4]", fmt.Sprint(globals, err))
	fmt.Println("PASS comprehension slice order, reverse strides, and omitted or explicit bounds")

	const rows = `rows = [[("a", [4]), ([], [5])]]
`
	const failed = `{mark(4, k): mark(5, v) for row in mark(3, rows) for (k, [v]) in row}`
	const receiver = `mark(1, 0)`
	const lower = `len([x for x in mark(2, [])])`
	const upper = `len([x for x in mark(6, [])])`
	const listReceiver = `[x for x in mark(1, [0, 1])]`
	const badLower = `[x for x in mark(2, [])]`
	const badUpper = `[x for x in mark(3, [])]`
	const zero = `len([x for x in mark(4, [])])`
	const badStep = `[x for x in mark(4, [])]`
	const negative = `mark(4, -1)`
	for _, tc := range []struct {
		receiver, lower, upper, step string
		errorPart, events            string
	}{
		{failed, lower, upper, "mark(7, 0)", "unhashable type: list", "[3, 4, 5, 4, 5]"},
		{receiver, failed, upper, "mark(7, 0)", "unhashable type: list", "[1, 3, 4, 5, 4, 5]"},
		{receiver, lower, failed, "mark(7, 0)", "unhashable type: list", "[1, 2, 3, 4, 5, 4, 5]"},
		{receiver, lower, upper, failed, "unhashable type: list", "[1, 2, 6, 3, 4, 5, 4, 5]"},
		{receiver, badLower, badUpper, zero, "invalid slice operand", "[1, 2, 3, 4]"},
		{listReceiver, badLower, badUpper, zero, "zero is not a valid slice step", "[1, 2, 3, 4]"},
		{listReceiver, badLower, badUpper, badStep, "invalid slice step", "[1, 2, 3, 4]"},
		{listReceiver, badLower, badUpper, negative, "invalid start index", "[1, 2, 3, 4]"},
		{listReceiver, lower, badUpper, negative, "invalid end index", "[1, 2, 3, 4]"},
	} {
		expression := fmt.Sprintf("(%s)[%s:%s:%s]", tc.receiver, tc.lower, tc.upper, tc.step)
		globals, err = run(mark + rows + "out = " + expression)
		checkError(err, tc.errorPart)
		require(globals["out"] == nil && globals["events"].String() == tc.events, fmt.Sprint(globals, err))
		outer := globals["rows"].(*starlark.List)
		inner := outer.Index(0).(*starlark.List)
		require(outer.Append(starlark.None) == nil && inner.Append(starlark.None) == nil,
			"failed slice operand left a comprehension iterator active")
	}
	fmt.Println("PASS slice operand failures, guard cleanup, and receiver/step/start/stop precedence")
}

func checkClauseOperands() {
	const mark = `events = []
def mark(tag, value):
    events.append(tag)
    return value
`
	globals, err := run(mark + `def run(x):
    def worker():
        result = [(x, y) for x in [mark(1, x) for x in x]
                  if x and [x for x in [mark(2, x)]]
                  for y in [x for x in [mark(3, x)]]]
        return (len(x), result)
    return worker()
out = run([0, 4])
`)
	require(err == nil && globals["out"].String() == "(2, [(4, 4)])" &&
		globals["events"].String() == "[1, 1, 2, 3]", fmt.Sprint(globals, err))
	globals, err = run(`out = {k: y for (k, v) in [x for x in [("a", 0), ("a", 1), ("a", 2)]]
       if v and [x for x in [v]]
       for y in {w: None for w in [v]}}`)
	require(err == nil && globals["out"].String() == `{"a": 2}`, fmt.Sprint(globals, err))
	_, err = run(`z = [8]
out = [x for x in [1] if [y for y in z] for z in []]`)
	checkError(err, "referenced before assignment")
	globals, err = run(`z = [8]
out = [x for x in [] if [y for y in z] for z in []]`)
	require(err == nil && globals["out"].String() == "[]", fmt.Sprint(globals, err))
	fmt.Println("PASS nested clause scope, forward shadowing, false filter skips, and dict iteration")

	const rows = `rows = [[("a", [4]), ([], [5])]]
`
	const failed = `{mark(4, k): mark(5, v) for row in mark(3, rows) for (k, [v]) in row}`
	for _, expr := range []string{
		"[row for row in " + failed + "]",
		"[item for row in rows for item in " + failed + "]",
		"{0: row for row in rows if " + failed + "}",
	} {
		globals, err = run(mark + rows + "out = " + expr)
		checkError(err, "unhashable type: list")
		require(globals["out"] == nil && globals["events"].String() == "[3, 4, 5, 4, 5]", fmt.Sprint(globals, err))
		outer := globals["rows"].(*starlark.List)
		inner := outer.Index(0).(*starlark.List)
		require(outer.Append(starlark.None) == nil && inner.Append(starlark.None) == nil,
			"failed comprehension clause left an iterator active")
	}

	globals, err = run(mark + `rows = [[1]]
def touch():
    mark(6, 0)
    rows[0] = []
    return True
out = [row for row in rows if [x for x in rows] if touch()]
`)
	checkError(err, "during iteration")
	require(globals["out"] == nil && globals["events"].String() == "[6]" &&
		globals["rows"].String() == "[[1]]", fmt.Sprint(globals, err))
	require(globals["rows"].(*starlark.List).Append(starlark.None) == nil,
		"failed outer filter left the prior iterator active")
	fmt.Println("PASS nested guard lifetime on a shared alias, retained effects, and failure unwind")
}

func checkHeads() {
	const mark = `events = []
def mark(tag, value):
    events.append(tag)
    return value
`
	globals, err := run(mark + `def run(x):
    result = [[mark(2, x) for x in mark(1, [x])] for x in x if x]
    return (len(x), result)
out = run([0, 4, 5])
`)
	require(err == nil && globals["out"].String() == "(3, [[4], [5]])" &&
		globals["events"].String() == "[1, 2, 1, 2]", fmt.Sprint(globals, err))
	globals, err = run(mark + `out = {len([x for x in mark(1, width)]): {"n": x for x in mark(2, [n])}
       for (width, n) in [([0], 40), ([0, 0], 50), ([0], 60), ([], 0)] if n}`)
	require(err == nil && globals["out"].String() == `{1: {"n": 60}, 2: {"n": 50}}` &&
		globals["events"].String() == "[1, 2, 1, 2, 1, 2]", fmt.Sprint(globals, err))
	fmt.Println("PASS nested head scope, skipped heads, key/value order, and overwrite in insertion order")

	const rows = `rows = [[("a", [4]), ([], [5])]]
`
	const failed = `{mark(4, k): mark(5, v) for row in mark(3, rows) for (k, [v]) in row}`
	for _, tc := range []struct {
		expression string
		errorPart  string
		events     string
	}{
		{"[" + failed + " for row in rows]", "unhashable type: list", "[3, 4, 5, 4, 5]"},
		{"{" + failed + `: [x for x in mark(1, [7])] for row in rows}`, "unhashable type: list", "[3, 4, 5, 4, 5]"},
		{`{[x for x in mark(1, [])]: [v for v in mark(2, [])][1] for row in rows}`, "out of range", "[1, 2]"},
		{`{[x for x in mark(1, [])]: [v for v in mark(2, [9])] for row in rows}`, "unhashable type: list", "[1, 2]"},
	} {
		globals, err = run(mark + rows + "out = " + tc.expression)
		checkError(err, tc.errorPart)
		require(globals["out"] == nil && globals["events"].String() == tc.events, fmt.Sprint(globals, err))
		outer := globals["rows"].(*starlark.List)
		inner := outer.Index(0).(*starlark.List)
		require(outer.Append(starlark.None) == nil && inner.Append(starlark.None) == nil,
			"failed head left a comprehension iterator active")
	}
	globals, err = run(mark + `out = {len([x for x in mark(1, [row])]):
       ([x for x in mark(2, [row])] if row else [x for x in mark(3, [])][1])
       for row in [1, 0, 2]}`)
	checkError(err, "out of range")
	require(globals["out"] == nil && globals["events"].String() == "[1, 2, 1, 3]", fmt.Sprint(globals, err))

	globals, err = run(mark + `rows = [[1]]
def touch():
    mark(6, 0)
    rows[0] = []
    return True
out = {len([x for x in rows]): touch() for row in rows}
`)
	checkError(err, "during iteration")
	require(globals["out"] == nil && globals["events"].String() == "[6]" &&
		globals["rows"].String() == "[[1]]", fmt.Sprint(globals, err))
	require(globals["rows"].(*starlark.List).Append(starlark.None) == nil,
		"failed head left the outer iterator active")
	fmt.Println("PASS key/value failure precedence, residual effects, and enclosing guard unwind")

	globals, err = run(`out = [[y for x in source if x or y for y in [2]] for source in [[1], [0]]]`)
	require(err == nil && globals["out"].String() == "[[2], [2]]", fmt.Sprint(globals, err))
	fmt.Println("PROFILE DIFFERENCE Go also retains comprehension locals across revisits to nested heads")
}

func checkDefaults() {
	const mark = `events = []
def mark(tag, value):
    events.append(tag)
    return value
`
	globals, err := run(mark + `def make(seed):
    def factory():
        def work(before=mark(1, seed[0]), seed=[mark(2, x) for x in seed],
                 *, data={x: mark(3, 3) for x in seed}):
            seed[0] += data[7]
            return (before, seed, data)
        return work
    return factory()
def use(f):
    a = f()
    b = f(before=0)
    return (a[0], b[0], a[1][0], b[1][0], len(b[2]))
f = make([7])
out = use(f)
`)
	require(err == nil && globals["out"].String() == "(7, 0, 13, 13, 1)" &&
		globals["events"].String() == "[1, 2, 3]", fmt.Sprint(globals, err))
	f := globals["f"].(*starlark.Function)
	globals.Freeze()
	require(f.ParamDefault(0).String() == "7" && f.ParamDefault(1).String() == "[13]" &&
		f.ParamDefault(2).String() == "{7: 3}", "unexpected stored defaults")
	checkError(f.ParamDefault(1).(*starlark.List).Append(starlark.None), "frozen list")
	checkError(f.ParamDefault(2).(*starlark.Dict).SetKey(starlark.None, starlark.None), "frozen hash table")
	fmt.Println("PASS enclosing captures, mixed default order, repeated omission, override, and freezing")

	globals, err = run(mark + `rows = [[("a", [4]), ([], [5])]]
def out(xs=[mark(2, 41) for x in mark(1, [40])],
        bad={mark(4, k): mark(5, v) for row in mark(3, rows) for (k, [v]) in row},
        *, later=mark(6, 0)):
    pass
`)
	checkError(err, "unhashable type: list")
	require(globals["out"] == nil && globals["events"].String() == "[1, 2, 3, 4, 5, 4, 5]",
		fmt.Sprint(globals, err))
	outer := globals["rows"].(*starlark.List)
	inner := outer.Index(0).(*starlark.List)
	require(outer.Append(starlark.None) == nil && inner.Append(starlark.None) == nil,
		"failed default left a comprehension iterator active")
	fmt.Println("PASS failing default skips later defaults and function binding, retaining effects and releasing guards")

	globals, err = run(`def f(value=[[y for x in source if x or y for y in [2]] for source in [[1], [0]]]):
    return value
out = f()
`)
	require(err == nil && globals["out"].String() == "[[2], [2]]", fmt.Sprint(globals, err))
	fmt.Println("PROFILE DIFFERENCE Go retains comprehension locals across revisits within a default")
}

func checkPatternAssignment() {
	const mark = `events = []
def mark(tag, value):
    events.append(tag)
    return value
`
	globals, err := run(mark + `def f(x):
    (x, [x, y]) = [mark(2, piece) for piece in mark(1, [8, [9, x]])]
    return (x, y)
out = f(4)
(payload, [countValue, _hidden]) = [mark(4, piece) for piece in mark(3, [[7], (2, 3)])]
`)
	require(err == nil && globals["out"].String() == "(9, 4)" && globals["payload"].String() == "[7]" &&
		globals["countValue"].String() == "2" && globals["events"].String() == "[1, 2, 2, 3, 4, 4]",
		fmt.Sprint(globals, err))
	fmt.Println("PASS comprehension RHS before nested function and module pattern writes, including repeated names")

	const assignment = `(a, [b, c], d) = [mark(3, [])[1] if fail else mark(2, x)
                  for row in mark(1, rows) for (fail, x) in row]
`
	for _, tc := range []struct {
		fail, errorPart, effects string
		wroteFirst               bool
	}{
		{"False", "too few values to unpack", "[1, 2, 2, 2]", true},
		{"True", "out of range", "[1, 2, 3]", false},
	} {
		rows := fmt.Sprintf("rows = [[(False, 5), (%s, [6]), (False, 7)]]\n", tc.fail)
		globals, err = run(mark + rows + assignment)
		checkError(err, tc.errorPart)
		if tc.wroteFirst {
			require(globals["a"] != nil && globals["a"].String() == "5", fmt.Sprint(globals, err))
		} else {
			require(globals["a"] == nil, fmt.Sprint(globals, err))
		}
		require(globals["b"] == nil && globals["c"] == nil && globals["d"] == nil &&
			globals["events"].String() == tc.effects, fmt.Sprint(globals, err))
		outer := globals["rows"].(*starlark.List)
		inner := outer.Index(0).(*starlark.List)
		require(outer.Append(starlark.None) == nil && inner.Append(starlark.None) == nil,
			"failed assignment left a comprehension iterator active")
	}
	_, err = run("out = a\n(a, b) = [x for x in [1, 2]]")
	checkError(err, "global variable a referenced before assignment")
	fmt.Println("PASS pattern mismatch keeps earlier writes, failed RHS writes no leaf, and guards unwind")
}

func checkMixedTargets() {
	const mark = `events = []
def mark(tag, value):
    events.append(tag)
    return value
`
	g, err := run(mark + `alias = [7]
table = {"old": 8}
def f(x):
    (x, [mark(2, x)[mark(3, 0)], table[mark(4, "new")]]) = [x for x in mark(1, [alias, [9, 10]])]
    return x[0]
result = f(None)
row = [10, 20]
([mark(6, row)[mark(7, 1)], saved], out) = [x for x in mark(5, [row, 12])]
`)
	require(err == nil && g["events"].String() == "[1, 2, 3, 4, 5, 6, 7]" &&
		g["result"].String() == "9" && g["alias"].String() == "[9]" &&
		g["table"].String() == `{"old": 8, "new": 10}` && g["row"].String() == "[10, 10]" &&
		g["saved"].String() == "20" && g["out"].String() == "12", fmt.Sprint(g, err))
	fmt.Println("PASS mixed targets see earlier name writes and snapshot each node before visiting its leaves")

	const setup = `xs = [7]
alias = xs
rows = [[0]]
`
	const target = `(a, mark(2, alias)[mark(3, 0)], [b, mark(4, alias)[mark(5, 8)]], mark(6, alias)[mark(7, 0)])`
	const badReceiver = `(a, mark(2, alias)[mark(3, 0)], [b, mark(4, [])[0][mark(5, 8)]], mark(6, alias)[mark(7, 0)])`
	const good = `[x for x in mark(1, [5, 9, [10, 11], 12])]`
	for _, tc := range []struct {
		target, rhs, message, trace, first, second, alias string
	}{
		{target, `[[][0] for row in mark(1, rows) for x in row]`, "out of range", "[1]", "", "", "[7]"},
		{target, `[x for x in mark(1, [5, 9, [10], 12])]`, "too few values to unpack", "[1, 2, 3]", "5", "", "[9]"},
		{target, good, "out of range", "[1, 2, 3, 4, 5]", "5", "10", "[9]"},
		{badReceiver, good, "out of range", "[1, 2, 3, 4]", "5", "10", "[9]"},
	} {
		g, err = run(mark + setup + tc.target + " = " + tc.rhs + "\nmark(99, 0)")
		checkError(err, tc.message)
		require(g["events"].String() == tc.trace && g["xs"] == g["alias"] && g["alias"].String() == tc.alias,
			fmt.Sprint(g, err))
		for name, want := range map[string]string{"a": tc.first, "b": tc.second} {
			value := g[name]
			require((value == nil && want == "") || (value != nil && value.String() == want), fmt.Sprint(g, err))
		}
		outer := g["rows"].(*starlark.List)
		inner := outer.Index(0).(*starlark.List)
		require(outer.Append(starlark.None) == nil && inner.Append(starlark.None) == nil,
			"failed RHS or target left a comprehension guard active")
	}
	fmt.Println("PASS failed RHS skips all leaves, and later unpack, receiver and store errors keep earlier writes")
}

func checkMixedTargetScope() {
	g, err := run(`i = 8
xs = [7]
rows = [0, 9]
def outer():
    alias = xs
    def inner():
        (i, alias[i]) = [i for i in rows]
        return i
    return inner()
out = (outer(), xs[0], i)
item = [6]
first = [item for item in item]
`)
	require(err == nil && g["out"].String() == "(0, 9, 8)" && g["first"].String() == "[6]",
		fmt.Sprint(g, err))

	g, err = run(`xs = [7]
alias = xs
rows = [0, 9, 10]
(i, alias[i], xs[8]) = [item for item in rows]
`)
	checkError(err, "out of range")
	require(g["i"].String() == "0" && g["xs"] == g["alias"] && g["alias"].String() == "[9]",
		fmt.Sprint(g, err))
	require(g["rows"].(*starlark.List).Append(starlark.None) == nil, "assignment left the RHS guard active")
	fmt.Println("PASS local shadowing, captured receiver, enclosing first iterable, and partial module writes")
}

func main() {
	checkLists()
	checkDictionaries()
	checkExpressionPositions()
	checkCallOperands()
	checkDisplayAndIndexOperands()
	checkSliceOperands()
	checkClauseOperands()
	checkHeads()
	checkDefaults()
	checkPatternAssignment()
	checkMixedTargets()
	checkMixedTargetScope()
}
