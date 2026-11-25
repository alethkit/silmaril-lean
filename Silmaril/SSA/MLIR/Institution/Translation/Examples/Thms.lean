module

public import Silmaril.SSA.MLIR.Institution.Translation.Examples.Defs
public import Silmaril.SSA.MLIR.Institution.Translation.Thms
public import Silmaril.SSA.MLIR.Arith.Examples.Defs
import Silmaril.Proofs.SSA.MLIR.Institution.Translation.Examples.Correctness

public section

namespace Silmaril.MLIR.Institution.Translation.Examples

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.Arith.Examples (i1 i8)

/-- The reduct agrees with the independently specified source arithmetic model. -/
theorem lower_reduct : lower.reduct Arith.model = model :=
  Proofs.MLIR.Institution.Translation.Examples.lower_reduct

theorem lower_satisfaction (e : Equation signature) :
    (lower.equation e).Holds Arith.model ↔ e.Holds model := by
  rw [← lower_reduct]
  exact lower.satisfaction Arith.model e

/-- Doubling inside an isolated region lowers correctly for every positive width. -/
theorem scopedDouble_denote (a w : Width) (x : BitVec a.val) (y : BitVec w.val) :
    (lower.term (scopedDouble a w)).denote Arith.model (Fin.cases x (fun _ => y)) = y + y := by
  change y * BitVec.ofNat w.val 2 = y + y
  exact BitVec.mul_two

theorem scopedDouble_i8 :
    (lower.term (scopedDouble i1 i8)).denote Arith.model (Fin.cases 1#1 (fun _ => 200#8)) =
      144#8 :=
  (scopedDouble_denote i1 i8 1#1 200#8).trans rfl

end Silmaril.MLIR.Institution.Translation.Examples
