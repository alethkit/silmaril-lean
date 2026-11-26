module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split.Defs
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Phi.Split

public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split

universe v w
variable {V W K J : Type w} [DecidableEq K]

/-- The selected incoming column gets the forwarding predecessor. -/
theorem Plan.rekey_selected (plan : Plan V W K J) :
    plan.rekey plan.header plan.predecessor = some plan.forward := by
  simp [Plan.rekey, Plan.selected]

/-- All other predecessor keys only undergo the original label renaming. -/
theorem Plan.rekey_other (plan : Plan V W K J) {pred : Option K} {target : K}
    (other : ¬ plan.selected pred target) : plan.rekey target pred = pred.map plan.label := by
  simp [Plan.rekey, other]

/-- Every column retains its operand under the register renaming, including
the selected column now read using the forwarding predecessor. -/
theorem Plan.operand_rename [DecidableEq J] (plan : Plan V W K J)
    (target : K) (pred : Option K) (row : Row V K) :
    (plan.renameRow target row).operand (plan.rekey target pred) =
      (row.operand pred).rename plan.register :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Phi.Split.operand_rename plan target pred row

variable {F : Type v} [DecidableEq V] [DecidableEq W] [DecidableEq J] [DecidableEq F]

theorem Plan.check_sound (plan : Plan V W K J) {source : Graph V K F} {target : Graph W J F}
    (ok : plan.check source target = true) : Checked plan source target := by
  simp only [Plan.check, Bool.and_eq_true, decide_eq_true_eq] at ok
  exact ⟨ok.1.1.1, ok.1.1.2, ok.1.2, ok.2⟩

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split
