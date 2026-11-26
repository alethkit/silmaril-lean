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

func source(shadowed, failed bool) string {
	var initialize, parameter, rebind, argument string
	if !failed {
		initialize = "    x = seed\n"
	}
	if shadowed {
		parameter, rebind, argument = "x", "        x = 0\n", "other"
	}
	return fmt.Sprintf(`original = [11, 22]
other = [33, 44]
notice = [0]
def make(seed):
%s    def relay(%s):
        marker = [17]
        def before():
            return marker
        def inner(early=[73], saved=x, late=[99]):
            alias = saved
            return alias[x]
        def after():
            return 41
        copy = inner
%s        return copy
    notice[0] = 1
    escaped = relay(%s)
    x = 1
    return escaped
escaped = make(original)
alias = escaped
result = alias()
override = escaped(0, [91, 92])
`, initialize, parameter, rebind, argument)
}

func recursiveSource(shadowed, malformed bool) string {
	var relayParameter, relayArgument, duplicate string
	if shadowed {
		relayParameter, relayArgument = "x", "near"
	}
	if malformed {
		duplicate = "saved, "
	}
	return fmt.Sprintf(`def noise():
    return 0
values = [11, 22]
near = [33, 44]
def factory(x, index):
    def relay(%s):
        def leaf(%ssaved=x):
            offset = index
            alias = x
            return saved[offset]
        return leaf
    return relay
relay_fn = factory(values, 1)
leaf_fn = relay_fn(%s)
result = leaf_fn()
`, relayParameter, duplicate, relayArgument)
}

func checkRecursive(opts *syntax.FileOptions) {
	for _, test := range []struct {
		shadowed bool
		result   string
	}{
		{false, "22"},
		{true, "44"},
	} {
		globals, err := starlark.ExecFileOptions(opts, new(starlark.Thread),
			"nested-suite.star", recursiveSource(test.shadowed, false), nil)
		require(err == nil && globals["result"].String() == test.result, globals)
	}
	fmt.Println("PASS grandchild default reads the forwarded binding or the nearer shadowing parameter")

	_, err := starlark.ExecFileOptions(opts, new(starlark.Thread),
		"duplicate-leaf-parameter.star", recursiveSource(false, true), nil)
	require(err != nil && strings.Contains(err.Error(), "duplicate parameter: saved"), err)
	fmt.Println("PASS duplicate grandchild parameter rejected")
}

func main() {
	opts := &syntax.FileOptions{}
	for _, test := range []struct {
		shadowed         bool
		result, override string
	}{
		{false, "22", "92"},
		{true, "33", "91"},
	} {
		globals, err := starlark.ExecFileOptions(opts, new(starlark.Thread),
			"forwarded-default.star", source(test.shadowed, false), nil)
		require(err == nil, err)
		require(globals["result"].String() == test.result && globals["override"].String() == test.override &&
			globals["alias"] == globals["escaped"] && globals["notice"].String() == "[1]", globals)
		require(globals["notice"].(*starlark.List).SetIndex(0, starlark.MakeInt(2)) != nil, globals)
	}
	fmt.Println("PASS saved value and live forwarded binding after escape, including explicit override and local shadowing")

	_, compiled, err := starlark.SourceProgramOptions(opts, "uninitialized-default.star",
		source(false, true), func(string) bool { return false })
	require(err == nil, err)
	partial, err := compiled.Init(new(starlark.Thread), nil)
	require(err != nil && strings.Contains(err.Error(), "local variable x referenced before assignment"), err)
	require(partial["escaped"] == nil && partial["alias"] == nil && partial["result"] == nil &&
		partial["notice"].String() == "[1]", partial)
	require(partial["notice"].(*starlark.List).SetIndex(0, starlark.MakeInt(2)) == nil, partial)
	fmt.Println("PASS uninitialized forwarded default retains the earlier visible mutation and prevents publication")

	checkRecursive(opts)
}
