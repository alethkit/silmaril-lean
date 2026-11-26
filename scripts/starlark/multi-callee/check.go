// Run from the pinned starlark-go checkout.
package main

import (
	"fmt"
	"strings"

	"go.starlark.net/starlark"
	"go.starlark.net/syntax"
)

const prefix = `def maker(box):
    def first(idx):
        idx, box[idx] = pair_one
        return seen
    return first
box = [3]
shared = box
one = maker(shared)
copy = one
def second(idx):
    idx, shared[idx] = pair_two
    return later
pair_one = (0, 9)
pair_two = (0, 12)
seen = 13
part1 = one(1)
`

const tail = "part2 = second(1)\npart3 = copy(1)\n"

func require(ok bool, detail any) {
	if !ok {
		panic(detail)
	}
}

func main() {
	filename := "trace.star"
	opts := &syntax.FileOptions{}
	globals, err := starlark.ExecFileOptions(opts, new(starlark.Thread), filename, prefix+"later = 14\n"+tail, nil)
	require(err == nil, err)
	require(globals["one"] == globals["copy"] && globals["box"] == globals["shared"], globals)
	require(globals["part1"].String() == "13" && globals["part2"].String() == "14" &&
		globals["part3"].String() == "13" && globals["box"].String() == "[9]", globals)
	require(globals["box"].(*starlark.List).Append(starlark.MakeInt(1)) != nil, "publication did not freeze the aliased list")
	fmt.Println("PASS interleaved root definitions, an escaped closure alias and a repeated call preserve the shared list and freeze it on publication")

	_, program, err := starlark.SourceProgramOptions(opts, filename, prefix+tail+"later = 14\n", func(string) bool { return false })
	require(err == nil, err)
	partial, err := program.Init(new(starlark.Thread), nil)
	require(err != nil && strings.Contains(err.Error(), "global variable later referenced before assignment"), err)
	require(partial["box"].String() == "[12]" && partial["part1"].String() == "13" &&
		partial["part2"] == nil && partial["part3"] == nil && partial["later"] == nil, partial)
	require(partial["box"].(*starlark.List).Append(starlark.MakeInt(1)) == nil, "Program.Init froze the failed module")
	fmt.Println("PASS later definition fails after mutation, retaining the earlier result and skipping the remaining calls")

	_, _, err = starlark.SourceProgramOptions(opts, filename, prefix+"later = 14\n"+tail+"one = second\n",
		func(string) bool { return false })
	require(err != nil && strings.Contains(err.Error(), "cannot reassign global one"), err)
	fmt.Println("PASS checked file syntax rejects overwriting an existing module binding")
}
