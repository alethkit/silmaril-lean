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

func nativeExpressions() {
	const setup = `events = []
def note(marker, value):
    events.append(marker)
    return value
`
	published, err := starlark.ExecFileOptions(&syntax.FileOptions{},
		&starlark.Thread{Name: "native expressions"}, "native.star", setup+`def use(xs=note(1, [])):
    xs.append(9)
    return xs
seed = note(2, [[]])
note(3, len(seed)) if seed else note(99, 0)
out = note(4, seed) or note(99, 0)
`, nil)
	require(err == nil, fmt.Sprint(err))
	require(published["events"].String() == "[1, 2, 3, 4]", "unexpected module expression order")
	root := published["out"].(*starlark.List)
	child := root.Index(0).(*starlark.List)
	require(published["seed"] == root, "assignment must retain the original list identity")
	for _, list := range []*starlark.List{root, child} {
		err := list.Append(starlark.None)
		require(err != nil && strings.Contains(err.Error(), "frozen list"), fmt.Sprint(err))
	}
	_, err = starlark.Call(&starlark.Thread{Name: "after publication"}, published["use"], nil, nil)
	require(err != nil && strings.Contains(err.Error(), "frozen list"), fmt.Sprint(err))
	fmt.Println("PASS native module order, branch selection, export aliases, and transitive freeze")

	// Observe partial globals and effects before a host chooses whether to freeze them.
	_, program, err := starlark.SourceProgramOptions(&syntax.FileOptions{}, "failure.star", setup+`out = len(note(1, 9))
note(99, 0)
`, func(string) bool { return false })
	require(err == nil, fmt.Sprint(err))
	partial, err := program.Init(&starlark.Thread{Name: "failing module"}, nil)
	require(err != nil && strings.Contains(err.Error(), "has no len"), fmt.Sprint(err))
	require(partial["out"] == nil && partial["events"].String() == "[1]", "failure must preserve effects without assigning out")
	fmt.Println("PASS native module assignment failure preserves earlier effects and skips later statements")
}

func main() {
	provider, err := starlark.ExecFileOptions(&syntax.FileOptions{},
		&starlark.Thread{Name: "provider"}, "a.star", `def read():
    return x
x = 7
_secret = []
def bump():
    _secret.append(1)
`, nil)
	require(err == nil, fmt.Sprint(err))
	load := func(_ *starlark.Thread, name string) (starlark.StringDict, error) {
		if name != "provider" {
			return nil, fmt.Errorf("unavailable module %s", name)
		}
		return provider, nil
	}
	initConsumer := func(src string) (starlark.StringDict, error) {
		return starlark.ExecFileOptions(&syntax.FileOptions{},
			&starlark.Thread{Name: "consumer", Load: load}, "b.star", src+"\n", nil)
	}

	result, err := initConsumer(`load("provider", get="read")
x = 99
out = get()`)
	require(err == nil && result["out"].String() == "7" && result["get"] == nil,
		"imported closure must keep its defining module, and load aliases are file-local")
	_, err = initConsumer(`load("provider", "bump")
bump()`)
	require(err != nil && strings.Contains(err.Error(), "frozen list"), fmt.Sprint(err))
	fmt.Println("PASS module publication freezes private globals and imports preserve closure globals")

	_, err = initConsumer(`load("provider", "_secret")`)
	require(err != nil && strings.Contains(err.Error(), "not exported"), fmt.Sprint(err))
	_, err = initConsumer(`load("provider", x="read")
x = 2`)
	require(err != nil && strings.Contains(err.Error(), "x"), fmt.Sprint(err))
	_, err = initConsumer(`load("provider", "unknown")`)
	require(err != nil && strings.Contains(err.Error(), "not found"), fmt.Sprint(err))
	_, err = initConsumer(`load("missing", "read")`)
	require(err != nil && strings.Contains(err.Error(), "unavailable module"), fmt.Sprint(err))
	fmt.Println("PASS private import, name collision, absent export, and host module failures")
	nativeExpressions()
}
