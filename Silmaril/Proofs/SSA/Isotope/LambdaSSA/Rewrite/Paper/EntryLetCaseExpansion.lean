module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.CaseExpansion.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Example.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Initial.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Endpoint.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Substitution.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Example.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Thms

/-! # A native duplication step obstructs repair of just the target -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetCaseExpansion

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift)
open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory
open Paper.WithEntryLet (Site ofRegion_comp_constructor)
open Paper.WithEntryLet.OperandExample hiding source corrected_square corrected_iterate
open Paper.WithEntryLet.CaseExpansion Paper.EntryLetObstruction
open Paper.Extension.Singleton (projection projectStep iterateChosen projectSquare_iff projection_map_desc_congr)
open SequencingObstruction (Instruction)

local notation "J" => projection Seed

set_option backward.isDefEq.respectTransparency false

private theorem discard_values (Γ : VCtx (Ty Empty)) :
    ∀ ⦃i A⦄, At [U] i A → Tm.BranchValue Γ (discardInput i) A := by
  intro i A hi
  cases i with
  | zero => cases Option.some.inj hi; exact .unit
  | succ i => simp [At] at hi

private theorem discard_typed {r : Region Instruction} (hr : ValueBranches [U] r [Bit])
    (Γ : VCtx (Ty Empty)) : ValueBranches Γ (r.substVars discardInput) [Bit] :=
  hr.substVars (discard_values Γ)

private theorem rename_discarded {r : Region Instruction} (hr : ValueBranches [U] r [Bit])
    (ρ : Nat → Nat) : (r.substVars discardInput).renameVars ρ = r.substVars discardInput := by
  rw [renameVars_substVars]
  exact Paper.SingletonReification.SingleCfg.singleton_subst hr.hasType rfl

private theorem duplicated_typed : ValueBranches [Bit] duplicatedRequest [Bit] :=
  .case (.var rfl) ((discard_typed flatStep_typed [Bit]).renameVars (Ren.wk [Bit] U))
    ((discard_typed flatStep_typed [Bit]).renameVars (Ren.wk [Bit] U))

theorem native_expansion : Paper.Eqv [Bit] (flatRecurringRequest.substVars discardInput) duplicatedRequest [Bit] :=
  (Paper.case_ignoring (A := U) (B := U) (i := 0) rfl (discard_typed flatStep_typed [Bit]).hasType).symm

theorem move_one_copy : (Site.leftArm .here).move duplicatedRequest = some oneMovedRequest := by
  have hm : Site.here.move (flatRecurringRequest.substVars discardInput) =
      some (movedRecurringRequest.substVars discardInput) := by
    rw [Site.move_substVars, move_recurring_request]
    rfl
  change (Site.here.move ((flatRecurringRequest.substVars discardInput).renameVars Nat.succ)).map
    (fun r => Region.case (.var 0) r ((flatRecurringRequest.substVars discardInput).renameVars Nat.succ)) =
      some (Region.case (.var 0) ((movedRecurringRequest.substVars discardInput).renameVars Nat.succ)
        ((flatRecurringRequest.substVars discardInput).renameVars Nat.succ))
  rw [renameVars_eq_substVars, Site.move_substVars, hm]
  simp only [Option.map_some, renameVars_eq_substVars]

theorem oneMovedRequest_typed : ValueBranches [Bit] oneMovedRequest [Bit] :=
  (Site.move_sound (.leftArm .here) duplicated_typed move_one_copy).1

theorem corrected_composite :
    Paper.WithEntryLet.Eqv [Bit] (flatRecurringRequest.substVars discardInput) oneMovedRequest [Bit] :=
  (Paper.Extension.Eqv.paper (Seed := Seed) native_expansion).trans
    (Site.move_sound (.leftArm .here) duplicated_typed move_one_copy).2

private theorem source_arms :
    source ≫ coprod.map (𝟙 X) forget =
      (sumIso U U).hom ≫ coprod.desc
        (discardArrow U ≫ ofRegion movedRequest_typed ≫ discardArrow U ≫ coprod.inr)
        (discardArrow U ≫ ofRegion flatRequest_typed ≫ discardArrow U ≫ coprod.inr) := by
  have hl : (sumCofan (Φ := Instruction) U U).inl ≫ forget = discardArrow U := by
    rw [sumCofan_inl]
    exact discard_comp_branchValue (.inl (.var rfl))
  have hr : (sumCofan (Φ := Instruction) U U).inr ≫ forget = discardArrow U := by
    rw [sumCofan_inr]
    exact discard_comp_branchValue (.inr (.var rfl))
  rw [source, Category.assoc, coprod.desc_comp]
  simp only [Category.assoc, taggedSource_forget]
  rw [← Category.assoc (sumCofan (Φ := Instruction) U U).inl forget, hl,
    ← Category.assoc (sumCofan (Φ := Instruction) U U).inr forget, hr]

theorem source_composite :
    source ≫ coprod.map (𝟙 X) forget = ofRegion oneMovedRequest_typed ≫ (sumIso U U).hom := by
  have hl := ofRegion_comp_constructor (.unit (Γ := [U])) movedStep_typed (discard_typed movedStep_typed [U])
  have hr := ofRegion_comp_constructor (.unit (Γ := [U])) flatStep_typed (discard_typed flatStep_typed [U])
  change discardArrow U ≫ _ = _ at hl hr
  rw [source_arms, ← movedTarget_eq, ← flatTarget_eq, ← Category.assoc (discardArrow U),
    ← Category.assoc (discardArrow U), hl, hr, ← coprod.desc_comp, ← Category.assoc,
    coprod_desc_ofRegion]
  congr 1
  apply (ofRegion_eq_iff _ oneMovedRequest_typed).2
  change Paper.Eqv [Bit] (.case (.var 0) ((movedRecurringRequest.substVars discardInput).renameVars
    (lift Nat.succ)) ((flatRecurringRequest.substVars discardInput).renameVars (lift Nat.succ)))
    oneMovedRequest [Bit]
  simp only [oneMovedRequest, rename_discarded movedStep_typed, rename_discarded flatStep_typed]
  exact .refl (ValueBranches.case (.var (i := 0) (rfl : At [Bit] 0 Bit))
    (discard_typed movedStep_typed [U, Bit]) (discard_typed flatStep_typed [U, Bit])).hasType

theorem no_target_repair (g : X ⟶ X ⨿ X) :
    source ≫ coprod.map (𝟙 X) forget ≠ forget ≫ g := by
  obtain ⟨r, hr, e⟩ := exists_ofRegion (g ≫ (sumIso U U).inv)
  have hg : g = ofRegion hr ≫ (sumIso U U).hom := by
    rw [← e, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have he : forget ≫ ofRegion hr = ofRegion (discard_typed hr [Bit]) :=
    ofRegion_comp_constructor (.unit (Γ := [Bit])) hr (discard_typed hr [Bit])
  intro hs
  rw [source_composite, hg, ← Category.assoc forget, he] at hs
  exact oneMovedRequest_no_image r ((ofRegion_eq_iff _ oneMovedRequest_typed).1
    ((cancel_mono (sumIso U U).hom).1 hs.symm))

theorem corrected_square :
    projectStep Seed source ≫ coprod.map (𝟙 ((J).obj X)) ((J).map forget) =
      (J).map forget ≫ projectStep Seed target := by
  have he : forget ≫ ofRegion flatStep_typed = ofRegion (discard_typed flatStep_typed [Bit]) :=
    ofRegion_comp_constructor (.unit (Γ := [Bit])) flatStep_typed (discard_typed flatStep_typed [Bit])
  apply (projectSquare_iff Seed source target forget).2
  rw [source_composite, target, ← Category.assoc forget, he, Functor.map_comp, Functor.map_comp]
  exact congrArg (· ≫ (J).map (sumIso U U).hom)
    ((Paper.Extension.Singleton.ofRegion_eq_iff Seed _ _).2 corrected_composite).symm

private theorem taggedSource_congr {p q : X ⟶ X} (h : (J).map p = (J).map q) :
    (J).map (taggedSource p) = (J).map (taggedSource q) := by
  simp only [taggedSource, Functor.map_comp]
  apply congrArg ((J).map (sumIso U U).hom ≫ ·)
  apply projection_map_desc_congr Seed <;> simp only [Functor.map_comp, h]

theorem source_repaired :
    ∃ f : D ⟶ X ⨿ D, projectStep Seed f = projectStep Seed source ∧
      f ≫ coprod.map (𝟙 X) forget = forget ≫ target := by
  let f := taggedSource (ofRegion flatRequest_typed)
  let e := sumIso (Φ := Instruction) U U
  let l : X ⟶ D := (sumCofan U U).inl
  let r : X ⟶ D := (sumCofan U U).inr
  have combine : coprod.desc l r = e.inv := by
    apply coprod.hom_ext
    · rw [coprod.inl_desc, ← sumCofan_inl_sumIso_hom U U, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · rw [coprod.inr_desc, ← sumCofan_inr_sumIso_hom U U, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have baseline : e.hom ≫ coprod.desc (l ≫ f) (r ≫ f) = f := by
    rw [← coprod.desc_comp, ← Category.assoc, combine, Iso.hom_inv_id, Category.id_comp]
  have same : (J).map source = (J).map f := by
    rw [← baseline]
    simp only [source, Functor.map_comp]
    apply congrArg ((J).map e.hom ≫ ·)
    apply projection_map_desc_congr Seed _ rfl
    simp only [Functor.map_comp]
    rw [taggedSource_congr Paper.WithEntryLet.flatRequest_arrow_eq_moved.symm]
  refine ⟨f, ?_, ?_⟩
  · unfold projectStep
    rw [same]
  · rw [target, flatTarget_eq]
    exact taggedSource_forget _

theorem corrected_iterate :
    iterateChosen Seed (projectStep Seed source) =
      (J).map forget ≫ iterateChosen Seed (projectStep Seed target) := by
  obtain ⟨f, hf, native⟩ := source_repaired
  rw [← hf]
  exact Paper.Extension.Singleton.uniformity_of_constructor_square Seed ⟨.unit, .unit, rfl⟩ f target native

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetCaseExpansion
