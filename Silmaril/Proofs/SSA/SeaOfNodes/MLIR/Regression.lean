module

import Silmaril.SSA.SeaOfNodes.MLIR.Thms

namespace Silmaril.SSA.SeaOfNodes.MLIR

open RVSDG (Origin extend)
open Diamond (Dataflow)
open Silmaril.MLIR.Arith (Env Width)

private def i8 : Width := ⟨8, by decide⟩
private def i16 : Width := ⟨16, by decide⟩

private abbrev args := inputPorts [i8, i16, i8]
private abbrev sigs : List (List (Diamond.Ty Width)) := List.replicate 4 [.value (.data i8)]

private def shared : Dataflow Op args [] sigs :=
  .cons (.constant 250) .nil
    (.cons (.binary .addi) (.cons (.arg .head) (.cons (.output ⟨0, by decide⟩ .head) .nil))
      (.cons (.binary .muli) (.cons (.output ⟨1, by decide⟩ .head) (.cons (.output ⟨1, by decide⟩ .head) .nil))
        (.cons (.binary .addi) (.cons (.output ⟨2, by decide⟩ .head) (.cons (.arg (.tail (.tail .head))) .nil))
          .nil)))

private def result : Origin args (extend [] sigs) (.value (.data i8)) := .output ⟨3, by decide⟩ .head
private def env : Env [i8, i16, i8] := .cons 20 (.cons 1000 (.cons 3 .nil))

-- The shared sum is bound once. Both operands of the multiply refer to it.
example : lower shared result =
    .letOp (.constant (w := i8) 250)
      (.letOp (.binary .addi (.there .here) .here)
        (.letOp (.binary .muli .here .here)
          (.letOp (.binary .addi .here (.there (.there (.there (.there (.there .here))))))
            (.yield .here)))) := rfl

-- (20 + 250) mod 256 = 14, then 14 * 14 + 3 = 199.
example : (lower shared result).denote env = 199 := by
  rw [lower_denote]
  rfl

end Silmaril.SSA.SeaOfNodes.MLIR
