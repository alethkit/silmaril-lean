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

func loopScopes() {
	const items = `def items(*values):
    return list(values)
`
	const shadow = items + "x = list()\ndef run():\n"
	const call = "out = run()\n"
	const unbound = "local variable x referenced before assignment"
	runtimeError(shadow+"    x\n    for x in items(7): pass\n"+call, unbound)
	runtimeError(shadow+"    for x in x: pass\n"+call, unbound)
	runtimeError(shadow+"    for x in items(): pass\n    return x\n"+call, unbound)
	fmt.Println("PASS a loop target shadows the outer name before, within and after an empty loop")

	values, err := execute(items + `def last(x, *values):
    for x in values: pass
    return x
def capture():
    def read(): return x
    for x in items(3, 4): pass
    return read()
nonempty = last(99, 1, 2)
empty = last(99)
captured = capture()
`)
	require(err == nil, fmt.Sprint(err))
	require(values["nonempty"].String() == "2" && values["empty"].String() == "99" &&
		values["captured"].String() == "4", fmt.Sprint(values))
	fmt.Println("PASS loop target visibility and a closure's capture of the target")

	values, err = execute(items + `def nested():
    for x in items(10, 20):
        for y in items(False, True):
            if y: break
            else: continue
            len(9)
    return x if y else len(9)
def early():
    for x in items(7, 8):
        return x
    len(9)
last = nested()
first = early()
`)
	require(err == nil, fmt.Sprint(err))
	require(values["last"].String() == "20" && values["first"].String() == "7", fmt.Sprint(values))
	runtimeError(items+"def run():\n    for x in items(7): len(x)\n"+call, "has no len")
	fmt.Println("PASS nested break and continue, early return, and loop body error")

	staticError("for x in list(): pass\n", "for loop not within a function")
	staticError("def run():\n    if False: break\n", "break not in a loop")
	staticError("def run():\n    for x in list():\n        def nested(): continue\n", "continue not in a loop")
	fmt.Println("PASS loop-control scope and top-level loop rejection")
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

	loopScopes()
}
