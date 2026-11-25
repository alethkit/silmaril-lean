// Run from the pinned starlark-go checkout.
package main

import (
	"fmt"
	"strings"

	"go.starlark.net/starlark"
	"go.starlark.net/syntax"
)

func run(src string) (starlark.StringDict, error) {
	predeclared := starlark.StringDict{}
	_, program, err := starlark.SourceProgramOptions(
		&syntax.FileOptions{}, "functions.star", src+"\n", predeclared.Has,
	)
	if err != nil {
		return nil, err
	}
	return program.Init(&starlark.Thread{Name: "functions"}, predeclared)
}

func require(ok bool, message string) {
	if !ok {
		panic(message)
	}
}

func checkError(err error, part string) {
	require(err != nil && strings.Contains(err.Error(), part), fmt.Sprintf("want %q, got %v", part, err))
}

func checkClosure() {
	g, err := run(`def factory(x):
    def get():
        return x
    before = get()
    x = 2
    return (before, get)
pair = factory(1)
out = pair[1]()
`)
	require(err == nil && g["out"].String() == "2" && g["pair"].(starlark.Tuple)[0].String() == "1",
		"closure did not retain the defining cell")
	g, err = run(`def get():
    return x
x = 42
def caller(x):
    return get()
out = caller(9)`)
	require(err == nil && g["out"].String() == "42", "call did not preserve lexical globals")
	_, err = run(`def get():
    return x
out = get()
x = 42`)
	checkError(err, "referenced before assignment")
	fmt.Println("PASS live lexical cells, escaped closures, and defining-module global slots")
}

func checkReentry() {
	g, err := run(`def maker(other):
    def f(x):
        return other(x)
    return f
def leaf(x):
    return x
b = maker(leaf)
a = maker(b)
out = a(1)`)
	checkError(err, "function f called recursively")
	require(g["a"] != g["b"], "the two function instances should differ")
	fmt.Println("PASS default recursion guard checks declaration identity")
}

func checkStoreAndFreeze() {
	g, err := run(`def f(xs):
    xs.append(7)
    return xs[12]
container = []
out = f(container)`)
	checkError(err, "out of range")
	require(g["container"].String() == "[7]", "effects before failure were lost")
	g, err = run(`def factory():
    xs = []
    def appender():
        xs.append(1)
    return appender
f = factory()`)
	require(err == nil, fmt.Sprint(err))
	g["f"].Freeze()
	_, err = starlark.Call(&starlark.Thread{Name: "frozen closure"}, g["f"], nil, nil)
	checkError(err, "frozen list")
	fmt.Println("PASS effects survive failure and freezing follows captured cells")
}

func main() {
	checkClosure()
	checkReentry()
	checkStoreAndFreeze()
}
