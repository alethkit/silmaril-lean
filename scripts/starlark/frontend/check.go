// Run from the pinned starlark-go checkout. The fixtures arrive from Lean.
package main

import (
	"encoding/json"
	"fmt"
	"os"

	"go.starlark.net/syntax"
)

type fixture struct {
	Name    string
	Source  string
	Accepts bool
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
	for _, f := range fixtures {
		_, err := (&syntax.FileOptions{}).Parse(f.Name+".star", []byte(f.Source), 0)
		if (err == nil) != f.Accepts {
			fmt.Fprintf(os.Stderr, "%s: want Go acceptance %t, got %v\n", f.Name, f.Accepts, err)
			failed = true
		}
	}
	if failed {
		os.Exit(1)
	}
	fmt.Printf("Pinned Go parser matched all %d fixture expectations\n", len(fixtures))
}
