module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.CollapseObstruction.Uniformity.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.CollapseObstruction.Rewrite
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Thms

/-! # Pure uniformity is independent of the current CFG η rules -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ColouredDivergence

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Semantics (extend)
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.CollapseObstruction
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.CollapseObstruction.Uniformity
open scoped Silmaril.Isotope.LambdaSSA.Region.CfgEta.CollapseObstruction
open Silmaril.DeBruijn (lift)
open CfgEta (fromNative toHom_eq_iff feedback)

private def env : Env := fun _ => markedPayload

private def otherPayload : Val := .inr .unit

private theorem env_typed : EnvTy [stateType] env := by
  intro i A hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    exact .inl .unit
  | succ i => simp [At] at hi

theorem local_square :
    CfgEta.Eqv [stateType] (selfBody.lsubst (liftLSubstVars mapLocal))
      (pureChange.lsubst (liftLSubstVars (fun _ => selfBody))) [stateType, resultType] :=
  .native (.base (.refl (.br (ℓ := 0) rfl pureChange_value.hasType)))

private def selfStep (_ : Fin 1) (v : Val) : Result := .jump 0 v

private theorem path_self (v : Val) (i : Nat) :
    path selfStep (.inr (0, v)) i = .inr (0, v) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [path, ih]; rfl

private theorem self_colour (v : Val) :
    finish selfStep (.inr (0, v)) = .diverges (if v = markedPayload then false else true) := by
  classical
  have hn : ¬ ∃ r, terminates selfStep (.inr (0, v)) r := by
    rintro ⟨r, i, hi⟩
    rw [path_self] at hi
    cases hi
  have hrec : recurrent selfStep (.inr (0, v)) ↔ v = markedPayload := by
    constructor
    · intro h
      obtain ⟨j, _, i, hi⟩ := h 0
      rw [path_self] at hi
      exact congrArg Prod.snd (Sum.inr.inj hi)
    · intro h
      subst v
      exact fun k => ⟨k, le_rfl, 0, path_self markedPayload k⟩
  rw [finish, dite_eq_right hn, hrec]
  by_cases h : v = markedPayload <;> simp [h]

private theorem eval_selfLoop : evalRegion selfLoop env = .diverges false := by
  change finish selfStep (.inr (0, markedPayload)) = _
  rw [self_colour, ite_eq_left rfl]

private theorem eval_changeThenLoop : evalRegion changeThenLoop env = .diverges true := by
  rw [changeThenLoop, evalRegion_lsubst pureChange_typed.hasType env_typed]
  change evalRegion (liftLSubstVars (fun _ => selfLoop) 0) (extend env otherPayload) = _
  have hrename : ∀ i, (extend env otherPayload) (lift Nat.succ i) = (extend env otherPayload) i := by
    intro i
    cases i <;> rfl
  rw [liftLSubstVars, evalRegion_renameVars selfLoop hrename]
  change finish selfStep (.inr (0, otherPayload)) = _
  rw [self_colour, ite_eq_right (show otherPayload ≠ markedPayload from by decide)]

theorem local_uniformity_obstruction :
    ¬ CfgEta.Eqv [stateType] selfLoop changeThenLoop [resultType] := by
  intro eq
  have obs := cfgEta_same eq env env_typed
  rw [eval_selfLoop, eval_changeThenLoop] at obs
  cases obs

set_option backward.isDefEq.respectTransparency false in
theorem local_quotient_square :
    selfBodyArrow ≫ changeLocalArrow = stateChangeArrow ≫ selfBodyArrow := by
  apply toHom_eq_iff.mpr
  intro i A hi
  change At [stateType] i A at hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    exact local_square
  | succ i => simp [At] at hi

set_option backward.isDefEq.respectTransparency false in
theorem changeLocal_left :
    fromNative.map (stateInterface.appendInl returnInterface) ≫ changeLocalArrow =
      stateChangeArrow ≫ fromNative.map (stateInterface.appendInl returnInterface) := by
  apply toHom_eq_iff.mpr
  intro i A hi
  change At [stateType] i A at hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    exact .native (.base (.refl (.br (ℓ := 0) rfl pureChange_value.hasType)))
  | succ i => simp [At] at hi

set_option backward.isDefEq.respectTransparency false in
theorem changeLocal_right :
    fromNative.map (stateInterface.appendInr returnInterface) ≫ changeLocalArrow =
      fromNative.map (stateInterface.appendInr returnInterface) := by
  apply toHom_eq_iff.mpr
  intro i A hi
  change At [resultType] i A at hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    exact .native (.base (.refl (.br (ℓ := 1) rfl (.var (i := 0) rfl))))
  | succ i => simp [At] at hi

theorem local_quotient_failure :
    feedback (X := stateInterface) (Y := returnInterface) selfBodyArrow ≠
      stateChangeArrow ≫ feedback (X := stateInterface) (Y := returnInterface) selfBodyArrow := by
  intro h
  exact local_uniformity_obstruction ((Quotient.exact h) (i := 0) (A := stateType) rfl)


open CfgEta.TypeCategory in
theorem pureReturn_witness (ε : Type) [HasEff Empty ε] (pe : ε) :
    PureReturn pe pureStateChange := by
  let hr := returnRegion_typed pureChange_value.hasType
  have he : ofRegion pureChange_typed = ofRegion hr :=
    (ofRegion_eq_iff pureChange_typed hr).mpr (.native (.base
      (returnRegion_branchValue pureChange_value).symm))
  exact ⟨.inr .unit, pureChange_value.hasType, .inr .unit, hr, he⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ColouredDivergence
