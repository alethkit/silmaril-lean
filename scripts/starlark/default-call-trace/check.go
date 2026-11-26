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

const prefix = `seed = [3]
def pick(required, value=seed, buffer=[1]):
    return value
saved = pick
first = saved(0)
def edit(index):
    index, seed[index] = patch
    return index
patch = (0, 8)
touched = edit(1)
replacement = [4]
override = saved(0, replacement)
`

func main() {
	opts := &syntax.FileOptions{}
	globals, err := starlark.ExecFileOptions(opts, new(starlark.Thread), "defaults.star",
		prefix+"again = saved(0)\nlater = 77\n", nil)
	require(err == nil, err)
	require(globals["pick"] == globals["saved"] && globals["seed"] == globals["first"] &&
		globals["seed"] == globals["again"] && globals["first"].String() == "[8]" &&
		globals["replacement"] == globals["override"] && globals["override"].String() == "[4]" &&
		globals["touched"].String() == "0", globals)
	err = globals["seed"].(*starlark.List).SetIndex(0, starlark.MakeInt(5))
	require(err != nil && strings.Contains(err.Error(), "frozen"), err)
	fmt.Println("PASS repeated omitted calls see the edited alias, explicit arguments override, and publication freezes")

	for _, control := range []struct{ call, diagnostic string }{
		{"saved(0, seed[1], 2, later)", "list index 1 out of range"},
		{"saved(0, 1, 2, 3)", "accepts at most 3 positional arguments"},
		{"saved()", "missing 1 argument (required)"},
	} {
		_, program, err := starlark.SourceProgramOptions(opts, "failure.star",
			prefix+"again = "+control.call+"\nlater = 77\n", func(string) bool { return false })
		require(err == nil, err)
		partial, err := program.Init(new(starlark.Thread), nil)
		require(err != nil && strings.Contains(err.Error(), control.diagnostic), err)
		require(partial["again"] == nil && partial["later"] == nil &&
			partial["first"] == partial["seed"] && partial["seed"].String() == "[8]" &&
			partial["override"].String() == "[4]", partial)
	}
	fmt.Println("PASS reached operand error precedes later operands and arity; prior effects survive each error")

	// Rebinding the defining local exercises an escaped defaulted closure.
	// This nested defaulted definition is beyond the checked source trace.
	const rebind = `def outer(seed):
    def pick(required, value=seed):
        return value
    saved = pick
    first = saved(0)
    seed = [91]
    return saved, first, seed
bundle = outer([3])
saved = bundle[0]
before = bundle[1]
replacement = bundle[2]
after = saved(0)
override = saved(0, replacement)
again = saved(0)
`
	globals, err = starlark.ExecFileOptions(opts, new(starlark.Thread), "rebind.star", rebind, nil)
	require(err == nil, err)
	require(globals["before"] == globals["after"] && globals["after"] == globals["again"] &&
		globals["again"].String() == "[3]" && globals["override"] == globals["replacement"] &&
		globals["override"].String() == "[91]", globals)
	fmt.Println("PASS the escaped alias reuses its saved value after the defining local is rebound")
}
