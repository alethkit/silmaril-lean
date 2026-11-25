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

func main() {
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
