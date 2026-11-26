module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split.Defs

public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split

universe v w
variable {V W K J : Type w} {F : Type v}
  [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J] [DecidableEq F]

theorem Plan.check_sound (plan : Plan V W K J) {source : Graph V K F} {target : Graph W J F}
    (ok : plan.check source target = true) : Checked plan source target := by
  simp only [Plan.check, Bool.and_eq_true, decide_eq_true_eq] at ok
  exact ⟨ok.1.1.1, ok.1.1.2, ok.1.2, ok.2⟩

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split
