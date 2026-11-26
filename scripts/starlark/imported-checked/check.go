// Run from the pinned Starlark-Go checkout with go run and this file's path.
package main

import (
	"fmt"
	"strings"

	"go.starlark.net/starlark"
	"go.starlark.net/syntax"
)

const producer = `data = [31]
def factory(value):
    def child(first, *rest, key=value, **extras):
        marked = [44]
        print(marked[0])
        probe = key[0]
        seen = value[0]
        print(probe, seen)
        return late
    copy = child
    value = [52]
    return copy
escaped = factory(data)
late = [83]
alias = escaped
result = alias(another=[61], *[data, data], **{"extra": late})
after = [99]
`

func require(ok bool, detail any) {
	if !ok {
		panic(detail)
	}
}

func check(warm bool, name, mapping string) {
	opts := &syntax.FileOptions{}
	thread := &starlark.Thread{}
	var events []string
	thread.Print = func(_ *starlark.Thread, msg string) {
		events = append(events, msg)
	}
	var cached starlark.StringDict
	var initializations, hits int
	thread.Load = func(_ *starlark.Thread, module string) (starlark.StringDict, error) {
		require(module == "producer.star", module)
		if cached != nil {
			hits++
			return cached, nil
		}
		initializations++
		globals, err := starlark.ExecFileOptions(opts, thread, module, producer, nil)
		if err == nil {
			cached = globals
		}
		return globals, err
	}
	if warm {
		_, err := thread.Load(thread, "producer.star")
		require(err == nil, err)
	}
	consumer := fmt.Sprintf(`load("producer.star", loaded=%q)
result = loaded(another=[71], *[17, 18], **%s)
late = [199]
`, name, mapping)
	_, program, err := starlark.SourceProgramOptions(opts, "consumer.star", consumer, func(string) bool { return false })
	require(err == nil, err)
	partial, err := program.Init(thread, nil)
	require(initializations == 1 && (hits == 1) == warm, []int{initializations, hits})
	if name == "absent" {
		require(err != nil && strings.Contains(err.Error(), "absent") && strings.Join(events, ",") == "44,31 52", err)
		require(partial["result"] == nil && partial["late"] == nil, partial)
	} else if mapping == `{"key": 8}` {
		require(err != nil && strings.Contains(err.Error(), "unhandled index operation"), err)
		require(strings.Join(events, ",") == "44,31 52,44" && partial["result"] == nil && partial["late"] == nil, partial)
	} else {
		require(err == nil, err)
		partial.Freeze()
		require(partial["result"] == cached["late"] && partial["late"].String() == "[199]" &&
			partial["loaded"] == nil && strings.Join(events, ",") == "44,31 52,44,31 52", partial)
		require(partial["late"].(*starlark.List).SetIndex(0, starlark.MakeInt(2)) != nil, partial)
	}
	require(cached["data"].(*starlark.List).SetIndex(0, starlark.MakeInt(2)) != nil, cached)
	require(cached["late"].(*starlark.List).SetIndex(0, starlark.MakeInt(2)) != nil, cached)
}

func main() {
	for _, warm := range []bool{false, true} {
		check(warm, "escaped", `{"extra": 9}`)
		check(warm, "escaped", `{"key": 8}`)
		check(warm, "absent", `{"extra": 9}`)
	}
	fmt.Println("PASS cold and cached imports preserve saved values, captured cells and producer globals")
	fmt.Println("PASS missing export and reached body error skip the consumer tail")
}
