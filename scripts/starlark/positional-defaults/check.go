// Run from the pinned starlark-go checkout.
package main

import (
	"fmt"
	"strings"

	"go.starlark.net/starlark"
	"go.starlark.net/syntax"
)

func require(ok bool, detail any) {
	if !ok {
		panic(detail)
	}
}

func main() {
	const source = `seed = [3]
def pick(seed, x=seed, buf=[1]):
    return x
saved = pick
seed[0] = 8
omitted = saved(0)
override = saved(0, [4])
again = saved(0)
`
	opts := &syntax.FileOptions{}
	globals, err := starlark.ExecFileOptions(opts, new(starlark.Thread), "defaults.star", source, nil)
	require(err == nil, err)
	require(globals["saved"] == globals["pick"] && globals["omitted"] == globals["seed"] &&
		globals["again"] == globals["omitted"] && globals["omitted"].String() == "[8]" &&
		globals["override"].String() == "[4]", globals)
	for _, args := range []starlark.Tuple{nil, {starlark.MakeInt(0), starlark.MakeInt(1), starlark.MakeInt(2), starlark.MakeInt(3)}} {
		_, err := starlark.Call(new(starlark.Thread), globals["saved"], args, nil)
		require(err != nil && strings.Contains(err.Error(), "argument"), err)
	}
	fmt.Println("PASS omitted values reuse the saved alias, explicit values override, and invalid arities fail")

	const failure = `def broken(a=[1], b=later, c=[3]):
    return a
later = 5
`
	_, program, err := starlark.SourceProgramOptions(opts, "failed-default.star", failure, func(string) bool { return false })
	require(err == nil, err)
	partial, err := program.Init(new(starlark.Thread), nil)
	require(err != nil && strings.Contains(err.Error(), "global variable later referenced before assignment"), err)
	require(partial["broken"] == nil && partial["later"] == nil, partial)
	fmt.Println("PASS definition-time error leaves the function and following global unbound")

	// The existing native runtime also supports mutation in function bodies
	// and defining-scope local rebinding outside the new source proof.
	const wider = `def outer(seed):
    def f(x=seed, acc=[0]):
        acc[0] += 1
        return (x, acc[0])
    seed = 14
    return f
saved = outer(7)
first = saved()
second = saved(9)
third = saved()
`
	mutable, err := starlark.ExecFileOptions(opts, new(starlark.Thread), "wider-defaults.star", wider, nil)
	require(err == nil, err)
	require(mutable["first"].String() == "(7, 1)" && mutable["second"].String() == "(9, 2)" &&
		mutable["third"].String() == "(7, 3)", mutable)
	_, err = starlark.Call(new(starlark.Thread), mutable["saved"], nil, nil)
	require(err != nil && strings.Contains(err.Error(), "frozen"), err)
	fmt.Println("PASS saved values survive defining-scope rebinding and mutable defaults retain identity and freeze")
}
