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

func liveProvenanceSource(arguments string) string {
	return fmt.Sprintf(`values = [0, 22]
def factory(values, index):
    def first(saved=values):
        return saved[index]
    alias = first
    marker = [17]
    copy = alias
    def replacement(required, offset=1, saved=values):
        return required[offset][saved[0]]
    first = replacement
    alias = 0
    first_value = copy()
    selected = first(%s)
    after = [99]
    return selected
result = factory(values, 1)
finished = [91]
`, arguments)
}

func checkLiveProvenance(opts *syntax.FileOptions) {
	globals, err := starlark.ExecFileOptions(opts, new(starlark.Thread),
		"live-local-copies.star", liveProvenanceSource("[[first_value]], offset=values[0]"), nil)
	require(err == nil && globals["result"].String() == "22" && globals["finished"].String() == "[91]", globals)
	fmt.Println("PASS mixed actuals use the rebound closure's named override and a saved default")

	for _, test := range []struct {
		arguments string
		errorText string
	}{
		{"", "function replacement missing 1 argument (required)"},
		{"[73], other=[80], required=[81]", `unexpected keyword argument "other"`},
		{"[73], required=[80], other=[81]", `multiple values for parameter "required"`},
		{"[73], other=[80], offset=[0][1], later=[77]", "index 1 out of range"},
		{"[73], [74], [75], [76], other=[80]", "3 positional arguments (4 given)"},
	} {
		_, compiled, err := starlark.SourceProgramOptions(opts, "rebound-local-error.star",
			liveProvenanceSource(test.arguments), func(string) bool { return false })
		require(err == nil, err)
		partial, err := compiled.Init(new(starlark.Thread), nil)
		require(err != nil && strings.Contains(err.Error(), test.errorText), err)
		require(partial["factory"] != nil && partial["result"] == nil && partial["finished"] == nil, partial)
	}
	_, _, err = starlark.SourceProgramOptions(opts, "repeated-keyword.star",
		liveProvenanceSource("[73], offset=[0][1], offset=2"), func(string) bool { return false })
	require(err != nil && strings.Contains(err.Error(), `keyword argument "offset" is repeated`), err)
	_, err = starlark.ExecFileOptions(opts, new(starlark.Thread), "nullary-keyword.star", `def empty():
    pass
result = empty(other=1)
`, nil)
	require(err != nil && strings.Contains(err.Error(), "accepts no arguments (1 given)"), err)
	fmt.Println("PASS operand error precedes binding, surplus positional arguments precede keywords, and repeated syntax is static")
}

func checkExplicitOperandOrder(opts *syntax.FileOptions) {
	for _, test := range []struct {
		operand string
		order   string
		error   string
	}{
		{"observe(2)", "1,2,3", `unexpected keyword argument "other"`},
		{"observe(2)[1]", "1,2", "index 1 out of range"},
	} {
		var observed []string
		thread := &starlark.Thread{
			Print: func(_ *starlark.Thread, msg string) { observed = append(observed, msg) },
		}
		source := fmt.Sprintf(`def observe(value):
    print(value)
    return [value]
def f(a, b=1):
    print("body")
value = f(observe(1), other=%s, b=observe(3))
`, test.operand)
		_, err := starlark.ExecFileOptions(opts, thread, "explicit-operand-order.star", source, nil)
		require(err != nil && strings.Contains(err.Error(), test.error), err)
		require(strings.Join(observed, ",") == test.order, observed)
	}
	fmt.Println("PASS Go evaluates explicit operands left to right once and skips the tail after an operand error")
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
	checkLiveProvenance(opts)
	checkExplicitOperandOrder(opts)
}
