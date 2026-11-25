module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.ProjectionExample.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.InstructionFree.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Naturality.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Feedback.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectionSimulation

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
open Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation
open Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.ProjectionExample
open scoped Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.ProjectionExample
open ContinuationContext (single)

private noncomputable def decode :
    (toInterface Empty).obj (ofType result ⨿ ofType payload) ⟶
      Paper.fromNative.obj ((single payload).append (single result)) :=
  (sumIso (Φ := Empty) result payload).inv.hom ≫
    Paper.fromNative.map (SyntacticCategory.iterationDispatchHom payload result)

set_option backward.isDefEq.respectTransparency false in
private theorem decode_after :
    repeatAfter.hom ≫ decode = Paper.fromNative.map ((single payload).appendInl (single result)) := by
  have hin : repeatAfter ≫ (sumIso (Φ := Empty) result payload).inv =
      (sumCofan (Φ := Empty) result payload).inr := by
    rw [repeatAfter, ← sumCofan_inr_sumIso_hom result payload, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hd := congrArg (Paper.fromCfgEta (Φ := Empty) (Γ := ([] : VCtx Types))).map
    (CfgEta.TypeCategory.iterationDispatch_inr (Φ := Empty) (Γ := []) payload result)
  rw [Functor.map_comp] at hd
  change repeatAfter.hom ≫ (sumIso (Φ := Empty) result payload).inv.hom ≫ _ = _
  rw [← Category.assoc]
  change (repeatAfter ≫ (sumIso (Φ := Empty) result payload).inv).hom ≫ _ = _
  rw [hin]
  exact hd

private theorem bound_left_shape {t : Tm Empty} :
    repeatBody.lsubst (liftLSubstVars (boundLocalMap t)) = .let₁ t repeatBody := by
  change ((Region.br 0 t).bindBranchArguments.renameVars (Silmaril.DeBruijn.lift Nat.succ)).substVars
    (Tm.singleSubst (.var 0)) = _
  rw [substVars_renameVars]
  have h : Tm.singleSubst (.var 0 : Tm Empty) ∘ Silmaril.DeBruijn.lift Nat.succ = Tm.var := by
    funext i
    cases i <;> rfl
  rw [h, substVars_var]
  rfl

private theorem repeatThenProject_typed : ValueBranches [state] repeatThenProject [payload, result] := by
  rw [repeatThenProject, bound_left_shape]
  exact .let₁ (projectRight_typed [])
    (.br (ℓ := 0) rfl (.var (i := 0) rfl))

private theorem projectThenRepeat_typed : ValueBranches [state] projectThenRepeat [payload, result] := by
  rw [projectThenRepeat, lsubst_bindBranchArguments_br]
  exact .let₁ (projectRight_typed [])
    (.br (ℓ := 0) rfl (.var (i := 0) rfl))

private theorem change_then_decoded :
    stateChange.hom ≫ Paper.fromNative.map ((single payload).appendInl (single result)) =
      Paper.singletonArrow projectThenRepeat_typed := by
  change Paper.toHom _ ≫ Paper.toHom _ = Paper.toHom _
  apply Paper.toHom_eq_iff.mpr
  intro i A hi
  change At [state] i A at hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    change Paper.Eqv [state]
      (compLSubst (fun _ => (Region.br 0 projectRight).bindBranchArguments) labelId 0)
      projectThenRepeat [payload, result]
    rw [compLSubst_id_right, projectThenRepeat, lsubst_bindBranchArguments_br]
    exact Paper.Eqv.refl (.let₁ (projectRight_typed [])
      (.br (ℓ := 0) rfl (.var (i := 0) rfl)))
  | succ i => simp [At] at hi

set_option backward.isDefEq.respectTransparency false in
private theorem decoded_left :
    (repeatBefore ≫ coprod.map (𝟙 (ofType result)) stateChange).hom ≫ decode =
      Paper.singletonArrow repeatThenProject_typed := by
  rw [repeatBefore, coprod.inr_map]
  change (stateChange.hom ≫ repeatAfter.hom) ≫ decode = _
  rw [Category.assoc, decode_after, change_then_decoded]

set_option backward.isDefEq.respectTransparency false in
theorem local_square_of_ordinary
    (comm : repeatBefore ≫ coprod.map (𝟙 (ofType result)) stateChange = stateChange ≫ repeatAfter) :
    Paper.Eqv [state, state] repeatThenProject projectThenRepeat [payload, result] := by
  have h := congrArg (fun f => f.hom ≫ decode) comm
  rw [decoded_left] at h
  change Paper.singletonArrow repeatThenProject_typed = (stateChange.hom ≫ repeatAfter.hom) ≫ decode at h
  rw [Category.assoc, decode_after, change_then_decoded] at h
  have atRoot : Paper.Eqv [state] repeatThenProject projectThenRepeat [payload, result] :=
    Paper.toHom_eq_iff.mp h (i := 0) (A := state) rfl
  have wk : Ren [state] [state, state] id := by
    intro i A hi
    cases i with
    | zero => exact hi
    | succ i => simp [At] at hi
  simpa only [renameVars_id] using atRoot.renameVars wk

theorem cfg_equation_of_ordinary
    (comm : repeatBefore ≫ coprod.map (𝟙 (ofType result)) stateChange = stateChange ≫ repeatAfter) :
    Paper.Extension.Eqv InstructionFreeStep [state] loopBefore loopAfter [result] := by
  let : HasEff Empty Bool := ⟨fun _ => true⟩
  have step : InstructionFreeStep [state] loopBefore loopAfter [result] :=
    .simulate (repeat_typed state [] [result])
      (repeat_typed state [state] [result]) (repeat_typed payload [state] [result])
      (projectRight_typed [state]) (.let₂ .var .var) (local_square_of_ordinary comm)
  exact .extra step.typed.1 step.typed.2 step

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectionSimulation
