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

func program(index int, defaultRead string) string {
	return fmt.Sprintf(`def make(seed):
    earlier = [13]
    offset = seed[%d]
    def inner(early=[14], saved=%s, last=[73]):
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
outer_a = [seed_a]
outer_b = [seed_b]
a = make(outer_a)
b = make(outer_b)
alias = a
first = alias()
second = b()
replacement = [7, 9]
override = a(0, replacement)
again = alias()
`, index, defaultRead)
}

func checkFailure(opts *syntax.FileOptions, source string, errorParts ...string) {
	_, compiled, err := starlark.SourceProgramOptions(opts, "wrapper-error.star",
		source, func(string) bool { return false })
	require(err == nil, err)
	partial, err := compiled.Init(new(starlark.Thread), nil)
	require(err != nil, partial)
	for _, part := range errorParts {
		require(strings.Contains(err.Error(), part), err)
	}
	require(partial["seed_a"].String() == "[3, 5]" && partial["seed_b"].String() == "[6, 8]" &&
		partial["a"] == nil && partial["b"] == nil && partial["alias"] == nil && partial["first"] == nil, partial)
	err = partial["seed_a"].(*starlark.List).SetIndex(0, starlark.MakeInt(0))
	require(err == nil, err)
}

func main() {
	opts := &syntax.FileOptions{}
	globals, err := starlark.ExecFileOptions(opts, new(starlark.Thread), "wrapper.star", program(0, "offset"), nil)
	require(err == nil, err)
	require(globals["a"] == globals["alias"] && globals["a"] != globals["b"] &&
		globals["first"].String() == "5" && globals["second"].String() == "8" &&
		globals["override"].String() == "9" && globals["again"].String() == "5", globals)
	err = globals["seed_a"].(*starlark.List).SetIndex(0, starlark.MakeInt(0))
	require(err != nil && strings.Contains(err.Error(), "frozen"), err)
	fmt.Println("PASS prefix initializes a saved default, suffix rebinds the live capture, and separate escaped calls publish")

	checkFailure(opts, program(1, "offset"), "index 1 out of range")
	fmt.Println("PASS prefix error stops the wrapper before child installation and leaves prior globals unfrozen")

	checkFailure(opts, program(0, "unused"), "unused", "before assignment")
	fmt.Println("PASS successful prefix leaves the suffix-only local uninitialized during defaults")
}
