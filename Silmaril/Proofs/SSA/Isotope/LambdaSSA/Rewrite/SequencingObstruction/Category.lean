module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Iteration.Instance.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Iteration.SequencingObstruction.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.SequencingObstruction
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueFamilies

/-! # The sequencing witness in the native category with chosen coproducts -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Sequencing

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region.SequencingObstruction
open Silmaril.DeBruijn (lift)
open Region SyntacticCategory
open CategoryTheory CategoryTheory.Limits

private abbrev resultType : Ty Empty := .unit
private abbrev sumType : Ty Empty := .coprod resultType stateType

private theorem singleFamily {Γ : VCtx (Ty Empty)} {A : Ty Empty} {L : LCtx (Ty Empty)}
    {r : Region Instruction} (hr : ValueBranches (A :: Γ) r L) :
    LSubst.ValueFamily Γ [A] L (fun _ => r) := by
  intro i B h
  have eq : B = A := List.mem_singleton.mp (List.mem_of_getElem? h)
  cases eq
  exact hr

private theorem weakenCapture {Γ : VCtx (Ty Empty)} {A : Ty Empty} {L : LCtx (Ty Empty)}
    {r : Region Instruction} (hr : ValueBranches (A :: Γ) r L) (D : Ty Empty) :
    ValueBranches (A :: D :: Γ) (r.renameVars (lift Nat.succ)) L :=
  valueFamily_liftVars (singleFamily hr) D (ℓ := 0) (A := A) rfl

private theorem body_valueBranches :
    ValueBranches [stateType] (iterationBody producer) [stateType, resultType] :=
  valueBranches_lsubst producer_valueBranches
    (singleFamily (iterationDispatch_valueBranches stateType resultType))

theorem sequencing_typed :
    HasType [stateType] unfolded [.unit] ∧ HasType [stateType] sequenced [.unit] := by
  let R : Fin 1 → Ty Empty := fun _ => stateType
  have hb := weakenCapture body_valueBranches stateType
  have hd := iterationDispatch_valueBranches (Φ := Instruction) (Γ := [stateType]) stateType resultType
  refine ⟨.cfg R body_valueBranches.hasType (fun _ => hb.hasType), ?_⟩
  exact (valueBranches_lsubst producer_valueBranches
    (singleFamily (.cfg R hd (fun _ => weakenCapture hb sumType)))).hasType

private def bareContinuation : Region Instruction :=
  .case (.var 0) (.br 0 (.var 0)) ((iterateRegion stateType producer).renameVars (lift Nat.succ))

private theorem bare_valueBranches :
    ValueBranches [sumType] bareContinuation [resultType] :=
  .case (A := resultType) (B := stateType) (.var (i := 0) rfl)
    (.br (ℓ := 0) rfl (.var (i := 0) rfl))
    (weakenCapture (iterateRegion_valueBranches producer_valueBranches) sumType)

private theorem returnOrRepeat_lift :
    bareContinuation.renameVars (lift Nat.succ) = returnOrRepeat := rfl

private theorem liftedContinuation_valueBranches :
    ValueBranches [sumType, stateType] returnOrRepeat [resultType] :=
  returnOrRepeat_lift ▸ weakenCapture bare_valueBranches stateType

theorem fixpoint_typed :
    HasType [stateType] (iterateRegion stateType producer) [.unit] ∧
      HasType [stateType] (producer.lsubst (fun _ => returnOrRepeat)) [.unit] :=
  ⟨(iterateRegion_valueBranches producer_valueBranches).hasType,
    (valueBranches_lsubst producer_valueBranches (singleFamily liftedContinuation_valueBranches)).hasType⟩

private abbrev Native := SyntacticCategory Instruction ([] : VCtx (Ty Empty))
private abbrev stateObj : Native := ofType stateType
private abbrev resultObj : Native := ofType resultType

private noncomputable def producerHom : stateObj ⟶ (ofType sumType : Native) :=
  ofRegion producer_valueBranches

private noncomputable def fixedHom : stateObj ⟶ resultObj :=
  iterate producerHom

private noncomputable def decoderHom : (ofType sumType : Native) ⟶ resultObj :=
  ofRegion bare_valueBranches

private theorem syntactic_inl :
    (sumCofan (Φ := Instruction) (Γ := []) resultType stateType).inl =
      ofRegion (.br (ℓ := 0) rfl (.inl (Tm.BranchValue.var (i := 0) rfl))) := by
  apply InducedCategory.hom_ext
  exact ContinuationContext.appendInl_sumTag resultType stateType

private theorem syntactic_inr :
    (sumCofan (Φ := Instruction) (Γ := []) resultType stateType).inr =
      ofRegion (.br (ℓ := 0) rfl (.inr (Tm.BranchValue.var (i := 0) rfl))) := by
  apply InducedCategory.hom_ext
  exact ContinuationContext.appendInr_sumTag resultType stateType

set_option backward.isDefEq.respectTransparency false in
private theorem decoder_inl :
    (sumCofan (Φ := Instruction) (Γ := []) resultType stateType).inl ≫ decoderHom =
      𝟙 resultObj := by
  rw [syntactic_inl]
  apply InducedCategory.hom_ext
  apply @Quotient.sound _ (continuationSetoid (Φ := Instruction) [] [resultType] [resultType])
  intro i A hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    have hl : HasType [resultType, resultType] (.br 0 (.var 0) : Region Instruction) [resultType] :=
      .br rfl (.var rfl)
    have hr := (weakenCapture (iterateRegion_valueBranches producer_valueBranches) resultType).hasType
    exact (SubstitutionEquiv.base (.caseInl (.var (i := 0) rfl) hl hr)).trans (.letValue (.var rfl) hl)
  | succ i => simp [At] at hi

set_option backward.isDefEq.respectTransparency false in
private theorem decoder_inr :
    (sumCofan (Φ := Instruction) (Γ := []) resultType stateType).inr ≫ decoderHom =
      fixedHom := by
  rw [syntactic_inr, fixedHom, producerHom, iterate_ofRegion]
  apply InducedCategory.hom_ext
  apply @Quotient.sound _ (continuationSetoid (Φ := Instruction) [] [stateType] [resultType])
  intro i A hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    have hl : HasType [resultType, stateType] (.br 0 (.var 0) : Region Instruction) [resultType] :=
      .br rfl (.var rfl)
    have hr := (weakenCapture (iterateRegion_valueBranches producer_valueBranches) stateType).hasType
    exact (SubstitutionEquiv.base (.caseInr (.var (i := 0) rfl) hl hr)).trans (.letValue (.var rfl) hr)
  | succ i => simp [At] at hi

set_option backward.isDefEq.respectTransparency false in
private theorem decoder_coprod :
    (sumIso resultType stateType).hom ≫ coprod.desc (𝟙 resultObj) fixedHom = decoderHom := by
  apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit resultType stateType)
  · rw [← Category.assoc, sumCofan_inl_sumIso_hom, coprod.inl_desc, decoder_inl]
  · rw [← Category.assoc, sumCofan_inr_sumIso_hom, coprod.inr_desc, decoder_inr]

set_option backward.isDefEq.respectTransparency false in
theorem categorical_fixpoint_obstruction :
    let X : SyntacticCategory Instruction ([] : VCtx (Ty Empty)) := ofType stateType
    let Y : SyntacticCategory Instruction ([] : VCtx (Ty Empty)) := ofType (Ty.unit : Ty Empty)
    ∃ f : X ⟶ Y ⨿ X, CategoryTheory.iterate f ≠ f ≫ coprod.desc (𝟙 Y) (CategoryTheory.iterate f) := by
  dsimp only
  refine ⟨producerHom ≫ (sumIso resultType stateType).hom, ?_⟩
  rw [iterate_comp_sumIso, Category.assoc]
  change fixedHom ≠ producerHom ≫ ((sumIso resultType stateType).hom ≫
    coprod.desc (𝟙 resultObj) fixedHom)
  rw [decoder_coprod]
  intro eq
  have he : ofRegion (iterateRegion_valueBranches producer_valueBranches) =
      ofRegion (valueBranches_lsubst producer_valueBranches (singleFamily liftedContinuation_valueBranches)) := by
    rw [← iterate_ofRegion producer_valueBranches]
    exact eq
  exact fixpoint_obstruction ((ofRegion_eq_iff _ _).mp he)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Sequencing
