module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Thms

/-! # A two-state fixture for duplicate-feedback collapse -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta.CollapseObstruction

scoped instance emptyInstructions : HasTy Empty (Ty Empty) where
  src instruction := instruction.elim
  trg instruction := instruction.elim

def stateType : Ty Empty := .coprod .unit .unit
def resultType : Ty Empty := .unit

def body : Region Empty :=
  .case (.var 0) (.br 1 (.inr .unit)) (.br 0 (.inl .unit))

theorem body_typed : ValueBranches [stateType] body [stateType, stateType, resultType] :=
  .case (A := Ty.unit) (B := Ty.unit) (.var (i := 0) rfl)
    (.br (ℓ := 1) rfl (.inr .unit)) (.br (ℓ := 0) rfl (.inl .unit))

def nested : Region Empty :=
  feedbackRegion [stateType] (feedbackRegion [stateType] (fun _ => body)) 0

def flat : Region Empty :=
  feedbackRegion [stateType] (fun _ => body.renameLabels Nat.pred) 0

end Silmaril.Isotope.LambdaSSA.Region.CfgEta.CollapseObstruction
