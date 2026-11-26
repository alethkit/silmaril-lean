// Run from the pinned starlark-go checkout.
package main

import (
	"fmt"
	"strings"

	"go.starlark.net/starlark"
	"go.starlark.net/syntax"
)

const setup = `def outer(box):
    def bridge():
        def leaf(idx):
            idx, box[idx] = pair
            return later
        return leaf
    return bridge
box = [3]
pair = (0, 9)
bridge_saved = outer(box)
saved = bridge_saved()
`

func run(source string, publish bool) (starlark.StringDict, error) {
	thread := &starlark.Thread{}
	if publish {
		return starlark.ExecFileOptions(&syntax.FileOptions{}, thread, "mixed-leaf.star", source, nil)
	}
	_, program, err := starlark.SourceProgramOptions(&syntax.FileOptions{}, "mixed-leaf.star", source, func(string) bool { return false })
	if err != nil {
		return nil, err
	}
	return program.Init(thread, nil)
}

func require(ok bool, failure any) {
	if !ok {
		panic(failure)
	}
}

// The owner update occurs after closure creation. This additional
// control uses a wider wrapper body than the checked module theorem.
func checkOwnerRebind() {
	const source = `def outer(box):
    def leaf(idx):
        idx, box[idx] = (0, 9)
        return box
    box = replacement
    return leaf
original = [3]
replacement = [4]
saved = outer(original)
out = saved(1)
`
	globals, err := run(source, true)
	require(err == nil, err)
	require(globals["original"].String() == "[3]" && globals["replacement"].String() == "[9]" &&
		globals["out"] == globals["replacement"], globals)
	fmt.Println("PASS an escaped closure uses the later value in its enclosing slot")
}

func main() {
	checkOwnerRebind()
	globals, err := run(setup+"later = 9\nout = saved(1)\n", true)
	require(err == nil, err)
	require(len(globals) == 7 && globals["box"].String() == "[9]" && globals["out"].String() == "9", globals)
	require(globals["box"].(*starlark.List).Append(starlark.MakeInt(10)) != nil, "publication did not freeze box")
	fmt.Println("PASS escaped closure observes the earlier local rebind and mutates the original alias, then publication freezes it")

	failure := setup + "out = saved(1)\nlater = 9\n"
	partial, err := run(failure, false)
	require(err != nil && strings.Contains(err.Error(), "global variable later referenced before assignment"), err)
	require(partial["out"] == nil && partial["later"] == nil && partial["box"].String() == "[9]", partial)
	require(partial["box"].(*starlark.List).Append(starlark.MakeInt(10)) == nil, "Program.Init froze its partial namespace")
	fmt.Println("PASS late return error retains the escaped store and skips the destination and later command")

	frozen, err := run(failure, true)
	require(err != nil && frozen["box"].String() == "[9]", fmt.Sprint(frozen, err))
	require(frozen["box"].(*starlark.List).Append(starlark.MakeInt(10)) != nil, "ExecFileOptions did not freeze its partial namespace")
	fmt.Println("DIALECT Go ExecFileOptions freezes the partial namespace on failure; Program.Init leaves the residual list mutable")
}
