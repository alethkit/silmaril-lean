module

public import Silmaril.SSA.MLIR.Frontend.Arith.Defs
public import Silmaril.SSA.MLIR.Arith.Examples.Defs

/-! Decoded fixtures and their expected intrinsic blocks. -/

@[expose] public section

namespace Silmaril.MLIR.Frontend.Arith.Examples

open Silmaril.MLIR.Arith (Block Env)
open Silmaril.MLIR.Arith.Examples (i1 i8)

/-- Compute `2 * x + x` with an unrelated first argument. -/
def triple : Program where
  inputs := [⟨"flag", 1⟩, ⟨"x", 8⟩]
  resultWidth := 8
  body := .letOp ⟨"two", 8⟩ (.constant 2)
    (.letOp ⟨"doubled", 8⟩ (.binary .muli "x" "two")
      (.letOp ⟨"total", 8⟩ (.binary .addi "doubled" "x") (.finish .ret "total" 8)))

def tripleBlock : Block [i1, i8] i8 :=
  .letOp (.constant 2#8)
    (.letOp (.binary .muli (.there (.there .here)) .here)
      (.letOp (.binary .addi .here (.there (.there (.there .here)))) (.yield .here)))

def tripleEnv : Env [i1, i8] := .cons 1#1 (.cons 100#8 .nil)

/-- Square the first input in an isolated region. The region parameter uses
an outer name with a different width. -/
def square : Program where
  inputs := [⟨"x", 8⟩, ⟨"arg", 1⟩]
  resultWidth := 8
  body := .letRegion ⟨"squared", 8⟩ "x" ⟨"arg", 8⟩
    (.letOp ⟨"product", 8⟩ (.binary .muli "arg" "arg") (.finish .yield "product" 8))
    (.finish .ret "squared" 8)

def squareBlock : Block [i8, i1] i8 :=
  .letRegion .here (.letOp (.binary .muli .here .here) (.yield .here)) (.yield .here)

end Silmaril.MLIR.Frontend.Arith.Examples
