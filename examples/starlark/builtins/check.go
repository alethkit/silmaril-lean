// Run from the pinned starlark-go checkout.
package main

import (
	"fmt"
	"strings"

	"go.starlark.net/starlark"
	"go.starlark.net/syntax"
)

func run(src string) (starlark.StringDict, error) {
	_, program, err := starlark.SourceProgramOptions(
		&syntax.FileOptions{}, "builtins.star", src+"\n", func(string) bool { return false },
	)
	if err != nil {
		return nil, err
	}
	return program.Init(&starlark.Thread{Name: "builtins"}, nil)
}

func require(ok bool, message string) {
	if !ok {
		panic(message)
	}
}

func checkError(err error, part string) {
	require(err != nil && strings.Contains(err.Error(), part), fmt.Sprintf("want %q, got %v", part, err))
}

func checkValues() {
	g, err := run(`def apply(len, x):
    return len(x)
alias = len
table = {len: "length", type: "type"}
out = (bool(), bool(alias), bool([]), bool({"a": 0}), len("é😀"),
       len(*[[1, 2]]), type(None), type(alias), list(), tuple(),
       list({"z": 1, "a": 2}), tuple({"z": 1, "a": 2}),
       apply(type, 0), table[alias], len([5], **{}))`)
	require(err == nil, fmt.Sprint(err))
	want := `(False, True, False, True, 6, 2, "NoneType", "builtin_function_or_method", [], (), ["z", "a"], ("z", "a"), "int", "length", 1)`
	require(g["out"].String() == want, fmt.Sprintf("want %s, got %s", want, g["out"]))
	fmt.Println("PASS universal callable values, shadowing, byte length, expansion, and ordered dictionary keys")
}

func checkCopy() {
	g, err := run(`inner = [1]
source = [inner]
copy = list(source)
packed = tuple(source)
source.append(2)
inner.append(3)
out = (source, copy, packed)`)
	require(err == nil, fmt.Sprint(err))
	require(g["out"].String() == "([[1, 3], 2], [[1, 3]], ([1, 3],))", fmt.Sprint(g["out"]))

	source := g["source"].(*starlark.List)
	source.Freeze()
	thread := &starlark.Thread{Name: "frozen input"}
	result, err := starlark.Call(thread, starlark.Universe["list"], starlark.Tuple{source}, nil)
	require(err == nil, fmt.Sprint(err))
	copy := result.(*starlark.List)
	require(copy != source && copy.Index(0) == source.Index(0), "copy did not preserve only inner alias")
	require(copy.Append(starlark.None) == nil, "fresh copy must be mutable")
	checkError(copy.Index(0).(*starlark.List).Append(starlark.None), "frozen")
	fmt.Println("PASS shallow allocation, mutable copy of a frozen source, and shared frozen descendants")
}

func checkFailure() {
	for _, tc := range []struct{ call, want string }{
		{"len()", "want 1"},
		{"bool(1, 2)", "want at most 1"},
		{"type(1, 2)", "want exactly 1"},
		{"len(None)", "has no len"},
		{`list("x")`, "want iterable"},
		{`tuple("x")`, "want iterable"},
		{`type(**{"x": 1})`, "does not accept keyword arguments"},
	} {
		_, err := run(tc.call)
		checkError(err, tc.want)
	}

	g, err := run(`events = []
len(events.append(1), events.append(2), ignored=events.append(3))`)
	checkError(err, "unexpected keyword arguments")
	require(g["events"].String() == "[1, 2, 3]", fmt.Sprint(g["events"]))
	fmt.Println("PASS arity, keyword and type errors preserve preceding argument effects")
}

func checkRangeConstructors() {
	g, err := run(`def note(label, value):
    events.append(label)
    return value
events = []
span = range(10, 3, -2)
xs = list(note(1, span))
ys = tuple(note(2, span[::-2]))
xs.append(0)
out = (list(range(0)), tuple(range(3, 1)), xs, ys, {ys: "sliced"}[(4, 8)], span[-1])`)
	require(err == nil, fmt.Sprint(err))
	want := `([], (), [10, 8, 6, 4, 0], (4, 8), "sliced", 4)`
	require(g["out"].String() == want && g["events"].String() == "[1, 2]", fmt.Sprint(g))
	fmt.Println("PASS empty, descending and sliced range materialization, mutability and tuple keys")

	const setup = `def note(label, value):
    events.append(label)
    return value
events = []
out = [99]
`
	for _, tc := range []struct{ call, want, effects string }{
		{"list(note(1, range(4)), note(2, 0), ignored=note(3, 0))", "unexpected keyword arguments", "[1, 2, 3]"},
		{"tuple(note(1, 9), note(2, range(4)))", "want at most 1", "[1, 2]"},
		{"list(note(1, 9))", "want iterable", "[1]"},
		{"list(note(1, range(4)), len(note(2, 9)), note(3, range(4)))", "has no len", "[1, 2]"},
	} {
		g, err := run(setup + "out[0] = " + tc.call)
		checkError(err, tc.want)
		require(g["out"].String() == "[99]" && g["events"].String() == tc.effects, fmt.Sprint(g))
	}
	fmt.Println("PASS operand failures precede constructor checks, then keyword, arity and type")
}

func main() {
	checkValues()
	checkCopy()
	checkFailure()
	checkRangeConstructors()
}
