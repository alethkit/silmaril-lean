module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.ProgressiveGraph

universe u v
variable {O : Type u}

/-- The two ordered contacts of a binary generator drawing. -/
def binaryCap (S : Signature.{u,v} O) (left right : O) : FixedCap S where
  profile :=
    { size := 2
      label i := if i.val = 0 then left else right
      x i := if i.val = 0 then 1 / 6 else 2 / 3
      ordered := by
        intro i j lt
        fin_cases i <;> fin_cases j <;> norm_num at * }
  inside i := by fin_cases i <;> norm_num [Set.mem_Ioo]

theorem binaryCap_types (S : Signature.{u,v} O) (left right : O) :
    (binaryCap S left right).types = [left, right] := rfl

end Silmaril.RuntimeWires.ProgressiveGraph
