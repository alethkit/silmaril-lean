// Run from the pinned starlark-go checkout. The fixtures arrive from Lean.
package main

import (
	"encoding/json"
	"fmt"
	"os"
	"strings"

	"go.starlark.net/starlark"
	"go.starlark.net/syntax"
)

type fixture struct {
	Name    string
	Source  string
	Accepts bool
	Module  *moduleControl
}

type moduleControl struct {
	Phase string
	Want  string
}

func checkModule(file *syntax.File, control moduleControl) error {
	program, err := starlark.FileProgram(file, func(string) bool { return false })
	if control.Phase == "validation" {
		if err != nil && strings.Contains(err.Error(), control.Want) {
			return nil
		}
		return fmt.Errorf("want validation error containing %q, got %v", control.Want, err)
	}
	if err != nil {
		return fmt.Errorf("unexpected validation error: %w", err)
	}

	globals, err := program.Init(new(starlark.Thread), nil)
	if control.Phase == "runtime" {
		if err != nil && strings.Contains(err.Error(), control.Want) && globals["out"] == nil {
			return nil
		}
		return fmt.Errorf("want runtime error containing %q with out unbound, got error %v and out %v",
			control.Want, err, globals["out"])
	}
	if control.Phase != "publication" {
		return fmt.Errorf("unknown module phase %q", control.Phase)
	}
	if err != nil {
		return fmt.Errorf("unexpected runtime error: %w", err)
	}
	globals.Freeze()
	out, ok := globals["out"].(starlark.Int)
	if !ok || out.String() != control.Want {
		return fmt.Errorf("want out to be integer %s, got %v", control.Want, globals["out"])
	}
	return nil
}

func main() {
	var fixtures []fixture
	if err := json.NewDecoder(os.Stdin).Decode(&fixtures); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	if len(fixtures) == 0 {
		fmt.Fprintln(os.Stderr, "no Starlark frontend fixtures")
		os.Exit(1)
	}
	failed := false
	modules := 0
	for _, f := range fixtures {
		file, err := (&syntax.FileOptions{}).Parse(f.Name+".star", []byte(f.Source), 0)
		if (err == nil) != f.Accepts {
			fmt.Fprintf(os.Stderr, "%s: want Go acceptance %t, got %v\n", f.Name, f.Accepts, err)
			failed = true
			continue
		}
		if f.Module != nil {
			modules++
			if err != nil {
				fmt.Fprintf(os.Stderr, "%s: module control needs a Go syntax tree: %v\n", f.Name, err)
				failed = true
				continue
			}
			if err := checkModule(file, *f.Module); err != nil {
				fmt.Fprintf(os.Stderr, "%s: %v\n", f.Name, err)
				failed = true
			}
		}
	}
	if failed {
		os.Exit(1)
	}
	fmt.Printf("Pinned Go matched %d parse expectations and %d module observations\n", len(fixtures), modules)
}
