module

public import Silmaril.SSA.MLIR.Arith.Defs

/-! Small arithmetic blocks used to check both lowerings. -/

@[expose] public section

namespace Silmaril.MLIR.Arith.Examples

def i1 : Width := ⟨1, by decide⟩
def i8 : Width := ⟨8, by decide⟩

/-- Implement doubling by adding the input to itself. -/
def doubleAdd (w : Width) : Block [w] w :=
  .letOp (.binary .addi .here .here) (.yield .here)

/-- Implement doubling by multiplying by a materialized constant. -/
def doubleMul (w : Width) : Block [w] w :=
  .letOp (.constant (BitVec.ofNat w.val 2))
    (.letOp (.binary .muli (.there .here) .here) (.yield .here))

/-- Square the second input in an isolated region, then add it to the original
input in the outer block. The first input is an unrelated one-bit value. -/
def squareAdd : Block [i1, i8] i8 :=
  .letRegion (.there .here) (.letOp (.binary .muli .here .here) (.yield .here))
    (.letOp (.binary .addi .here (.there (.there .here))) (.yield .here))

end Silmaril.MLIR.Arith.Examples
