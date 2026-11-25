// Run from the pinned starlark-go checkout.
package main

import (
	"fmt"
	"strings"

	"go.starlark.net/starlark"
	"go.starlark.net/syntax"
)

func require(ok bool, message string) {
	if !ok {
		panic(message)
	}
}

func execute(source string) (starlark.StringDict, error) {
	thread := &starlark.Thread{Load: func(_ *starlark.Thread, label string) (starlark.StringDict, error) {
		if label != "dep" {
			return nil, fmt.Errorf("unexpected load %s", label)
		}
		return starlark.StringDict{"provided": starlark.MakeInt(7)}, nil
	}}
	return starlark.ExecFileOptions(&syntax.FileOptions{}, thread, "scope.star", source, nil)
}

func runtimeError(source, want string) {
	_, err := execute(source)
	_, runtime := err.(*starlark.EvalError)
	require(runtime && strings.Contains(err.Error(), want), fmt.Sprint(err))
}

func staticError(source, want string) {
	_, _, err := starlark.SourceProgramOptions(&syntax.FileOptions{}, "scope.star", source,
		func(string) bool { return false })
	require(err != nil && strings.Contains(err.Error(), want), fmt.Sprint(err))
}

func main() {
	values, err := execute(`value = "global"
def outer(value):
    def middle():
        def inner(value=value):
            return value if ready else "wrong"
        return inner
    value = "updated"
    return middle
middle = outer("initial")
inner = middle()
ready = True
inner()
out = inner()
explicit = inner(value="caller")
`)
	require(err == nil, fmt.Sprint(err))
	require(values["out"] == starlark.String("updated") && values["explicit"] == starlark.String("caller"),
		"defaults must see the updated outer slot and permit an explicit override")
	fmt.Println("PASS transitive captured locals, defining-scope defaults, and a forward global")

	runtimeError("out = len(\"x\")\nlen = 1\n", "global variable len referenced before assignment")
	runtimeError(`x = 8
def f():
    if False:
        x = 1
    return x
out = f()
`, "local variable x referenced before assignment")
	runtimeError("def f(other=other): pass\nother = 1\nf()\n", "global variable other referenced before assignment")
	runtimeError("out = imported\nload(\"dep\", imported=\"provided\")\n", "local variable imported referenced before assignment")
	fmt.Println("PASS unbound errors for a shadowed built-in, a local, a default, and a load alias")

	staticError("def f():\n    if False:\n        missing()\n", "undefined: missing")
	staticError("a = 1\ndef a(): pass\n", "cannot reassign global a")
	staticError("load(\"dep\", imported=\"provided\")\nimported = 1\n", "cannot reassign local imported")
	fmt.Println("PASS undefined name in skipped code and duplicate binding rejection")

	values, err = execute("def f(): return imported\nload(\"dep\", imported=\"provided\")\nout = f()\n")
	require(err == nil && values["out"].String() == "7" && values["imported"] == nil, fmt.Sprint(values, err))
	fmt.Println("PASS a closure sees a later file alias, and the alias is not exported")

	// This order differs from the pinned prose spec, which prohibits either order.
	values, err = execute("imported = 1\nload(\"dep\", imported=\"provided\")\n")
	require(err == nil && values["imported"].String() == "1", fmt.Sprint(values, err))
	fmt.Println("DIALECT pinned Go accepts a load alias after an already-bound global of the same name")
}
