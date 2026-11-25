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

func main() {
	checkLists()
	checkDictionaries()
}
