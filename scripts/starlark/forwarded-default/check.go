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

func recursiveSource(shadowed, malformed, failed bool) string {
	var relayParameter, relayArgument, duplicate, leading string
	if shadowed {
		relayParameter, relayArgument = "x", "near"
	}
	if malformed {
		duplicate = "saved, "
	}
	if failed {
		leading = "    marker = [73]\n    broken = marker[1]\n    later = [99]\n"
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
%s    copy = relay
    return copy
relay_fn = factory(values, 1)
leaf_fn = relay_fn(%s)
result = leaf_fn()
`, relayParameter, duplicate, leading, relayArgument)
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
			"nested-suite.star", recursiveSource(test.shadowed, false, false), nil)
		require(err == nil && globals["result"].String() == test.result, globals)
	}
	fmt.Println("PASS grandchild default reads the forwarded binding or the nearer shadowing parameter")

	_, err := starlark.ExecFileOptions(opts, new(starlark.Thread),
		"duplicate-leaf-parameter.star", recursiveSource(false, true, false), nil)
	require(err != nil && strings.Contains(err.Error(), "duplicate parameter: saved"), err)
	fmt.Println("PASS duplicate grandchild parameter rejected")

	_, compiled, err := starlark.SourceProgramOptions(opts, "nested-suite-error.star",
		recursiveSource(false, false, true), func(string) bool { return false })
	require(err == nil, err)
	partial, err := compiled.Init(new(starlark.Thread), nil)
	require(err != nil && strings.Contains(err.Error(), "index 1 out of range"), err)
	require(partial["factory"] != nil && partial["relay_fn"] == nil && partial["leaf_fn"] == nil &&
		partial["result"] == nil, partial)
	fmt.Println("PASS first reached suite error skips the escaped call and later module commands")
}

func aliasedCallSource(arguments string, index int) string {
	return fmt.Sprintf(`values = [11, 22]
def factory(x, index):
    outer_mark = [17]
    def relay():
        def leaf(saved=x):
            alias = [x]
            return saved[index]
        copy = leaf
        value = copy(%s)
        after = [value]
        return after[0]
    relay_copy = relay
    outer_value = relay_copy()
    outer_after = [outer_value]
    return outer_after[0]
result = factory(values, %d)
finished = [99]
`, arguments, index)
}

func checkAliasedCalls(opts *syntax.FileOptions) {
	globals, err := starlark.ExecFileOptions(opts, new(starlark.Thread),
		"aliased-positional-call.star", aliasedCallSource("", 1), nil)
	require(err == nil && globals["result"].String() == "22" && globals["finished"].String() == "[99]", globals)
	fmt.Println("PASS two local alias calls return through the saved default and forwarded index")

	for _, test := range []struct {
		arguments string
		index     int
		errorText string
	}{
		{"[73], [0][1], [99]", 1, "index 1 out of range"},
		{"[73], [74]", 1, "positional argument (2 given)"},
		{"", 3, "index 3 out of range"},
	} {
		_, compiled, err := starlark.SourceProgramOptions(opts, "aliased-call-error.star",
			aliasedCallSource(test.arguments, test.index), func(string) bool { return false })
		require(err == nil, err)
		partial, err := compiled.Init(new(starlark.Thread), nil)
		require(err != nil && strings.Contains(err.Error(), test.errorText), err)
		require(partial["factory"] != nil && partial["result"] == nil && partial["finished"] == nil, partial)
	}
	fmt.Println("PASS operand error precedes arity, and a reached inner body error skips the module tail")
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
	checkAliasedCalls(opts)
}
