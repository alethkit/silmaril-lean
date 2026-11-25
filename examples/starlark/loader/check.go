// Run from the pinned starlark-go checkout.
package main

import (
	"fmt"
	"slices"
	"strings"

	"go.starlark.net/starlark"
	"go.starlark.net/syntax"
)

type entry struct {
	source string
	labels map[string]string
}

// Starlark specifies a host boundary. This fixture supplies the same finite
// manifest, cycle and success-only caching policy as the Lean model.
type loader struct {
	manifest map[string]entry
	cache    map[string]starlark.StringDict
	runs     map[string]int
	partial  map[string]starlark.StringDict
}

func newLoader(manifest map[string]entry) *loader {
	return &loader{manifest, map[string]starlark.StringDict{}, map[string]int{}, map[string]starlark.StringDict{}}
}

func (l *loader) load(id string, path []string) (starlark.StringDict, error) {
	if slices.Contains(path, id) {
		return nil, fmt.Errorf("dependency cycle: %s", strings.Join(append(slices.Clone(path), id), " -> "))
	}
	if cached, ok := l.cache[id]; ok {
		return cached, nil
	}
	item, ok := l.manifest[id]
	if !ok {
		return nil, fmt.Errorf("unknown module %s", id)
	}
	_, program, err := starlark.SourceProgramOptions(&syntax.FileOptions{}, id+".star",
		item.source+"\n", func(string) bool { return false })
	if err != nil {
		return nil, err
	}
	path = append(slices.Clone(path), id)
	thread := &starlark.Thread{Name: id, Load: func(_ *starlark.Thread, label string) (starlark.StringDict, error) {
		target, ok := item.labels[label]
		if !ok {
			return nil, fmt.Errorf("%s has no label %s", id, label)
		}
		return l.load(target, path)
	}}
	l.runs[id]++
	globals, err := program.Init(thread, nil)
	if err != nil {
		l.partial[id] = globals
		return nil, err
	}
	globals.Freeze()
	for name := range globals {
		if strings.HasPrefix(name, "_") {
			delete(globals, name)
		}
	}
	l.cache[id] = globals
	return globals, nil
}

func require(ok bool, message string) {
	if !ok {
		panic(message)
	}
}

func requireError(err error, part string) {
	require(err != nil && strings.Contains(err.Error(), part), fmt.Sprintf("want %q, got %v", part, err))
}

func checkDiamond() {
	l := newLoader(map[string]entry{
		"root": {`load("route", left="out")
load("right", right="out")
load("again", again="out")
out = (left, right, again)`, map[string]string{"route": "left", "right": "right", "again": "leaf"}},
		"left": {`load("route", leaf="out")
out = leaf`, map[string]string{"route": "leaf"}},
		"right": {`load("leaf", leaf="out")
out = leaf`, map[string]string{"leaf": "leaf"}},
		"leaf": {"out = []", nil},
	})
	root, err := l.load("root", nil)
	require(err == nil, fmt.Sprint(err))
	result := root["out"].(starlark.Tuple)
	require(result[0] == result[1] && result[1] == result[2] && l.runs["leaf"] == 1,
		"the diamond and third alias must share a single leaf initialization")
	_, err = l.load("root", nil)
	require(err == nil && l.runs["root"] == 1, "the root must also be cached")
	requireError(result[0].(*starlark.List).Append(starlark.None), "frozen")
	fmt.Println("PASS requester-relative diamond, canonical alias reuse and frozen shared publication")
}

func checkCycle() {
	l := newLoader(map[string]entry{
		"a": {"out = []\nload(\"next\", dep=\"out\")", map[string]string{"next": "b"}},
		"b": {"out = []\nload(\"next\", dep=\"out\")", map[string]string{"next": "a"}},
	})
	_, err := l.load("a", nil)
	requireError(err, "a -> b -> a")
	require(len(l.cache) == 0 && l.partial["a"]["out"] != nil && l.partial["b"]["out"] != nil,
		"the failed cycle must retain initial effects and publish neither module")
	fmt.Println("PASS cycle rejects re-entry after earlier commands run")
}

func checkFailure() {
	l := newLoader(map[string]entry{
		"root": {`load("good", g="out")
load("bad", b="out")
out = []`, map[string]string{"good": "good", "bad": "bad"}},
		"good": {"out = []", nil},
		"bad":  {"out = []\nout.append(1)\nout[2]", nil},
	})
	_, err := l.load("root", nil)
	requireError(err, "out of range")
	first := l.partial["bad"]["out"].(*starlark.List)
	require(first.String() == "[1]" && len(l.cache) == 1 && l.cache["good"] != nil,
		"cache only the successful provider and retain the failed module's effect")
	require(first.Append(starlark.None) == nil, "failure must skip the publication freeze")
	_, err = l.load("root", nil)
	requireError(err, "out of range")
	require(l.runs["good"] == 1 && l.runs["bad"] == 2 && l.partial["bad"]["out"] != first,
		"the retry must reuse the successful provider and initialize the failed module again")
	fmt.Println("PASS failed initializer propagation, prior effects, and retry without failure caching")
}

func main() {
	checkDiamond()
	checkCycle()
	checkFailure()
}
