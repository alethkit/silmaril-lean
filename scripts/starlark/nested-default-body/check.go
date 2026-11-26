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

func program(defaultRead string) string {
	return `def make(seed):
    def inner(early=[13], saved=` + defaultRead + `, last=[73]):
        picked = saved[offset]
        buffer = [picked]
        answer = buffer[seed]
        repeat_read = saved[offset]
        return answer
    seed = 0
    offset = 0
    unused = 42
    offset = 1
    return inner
seed_a = [3, 5]
seed_b = [6, 8]
a = make(seed_a)
b = make(seed_b)
alias = a
first = alias()
second = b()
replacement = [7, 9]
override = a(0, replacement)
again = alias()
`
}

func main() {
	opts := &syntax.FileOptions{}
	globals, err := starlark.ExecFileOptions(opts, new(starlark.Thread), "local.star", program("seed"), nil)
	require(err == nil, err)
	require(globals["a"] == globals["alias"] && globals["a"] != globals["b"] &&
		globals["first"].String() == "5" && globals["second"].String() == "8" &&
		globals["override"].String() == "9" && globals["again"].String() == "5", globals)
	err = globals["seed_a"].(*starlark.List).SetIndex(0, starlark.MakeInt(0))
	require(err != nil && strings.Contains(err.Error(), "frozen"), err)
	fmt.Println("PASS separate escaping activations read a later-initialized, rebound local alongside the saved default and parameter capture")

	_, compiled, err := starlark.SourceProgramOptions(opts, "local-error.star",
		program("offset"), func(string) bool { return false })
	require(err == nil, err)
	partial, err := compiled.Init(new(starlark.Thread), nil)
	require(err != nil && strings.Contains(err.Error(), "offset") && strings.Contains(err.Error(), "before assignment"), err)
	require(partial["seed_a"].String() == "[3, 5]" && partial["seed_b"].String() == "[6, 8]" &&
		partial["a"] == nil && partial["b"] == nil && partial["alias"] == nil && partial["first"] == nil, partial)
	err = partial["seed_a"].(*starlark.List).SetIndex(0, starlark.MakeInt(0))
	require(err == nil, err)
	fmt.Println("PASS reading that local as a default fails during definition, retains earlier globals unfrozen, and prevents escape")
}
