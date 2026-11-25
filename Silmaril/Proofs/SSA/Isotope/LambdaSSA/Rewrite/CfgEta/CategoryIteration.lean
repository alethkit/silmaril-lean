module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Thms

/-! # The copair and fixpoint equations in the CFG η category -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Region.CfgEta (Eqv TypeCategory fromNative toHom_eq_iff)
open Region.CfgEta.TypeCategory
open Silmaril.DeBruijn (lift)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}
  {A B C : τ} {r s : Region Φ}

theorem ofRegion_eq_iff (hr : ValueBranches (A :: Γ) r [B]) (hs : ValueBranches (A :: Γ) s [B]) :
    ofRegion hr = ofRegion hs ↔ Eqv (A :: Γ) r s [B] := by
  constructor
  · intro h
    exact (toHom_eq_iff.mp (congrArg InducedCategory.Hom.hom h)) (i := 0) (A := A) rfl
  · intro h
    apply InducedCategory.hom_ext
    apply toHom_eq_iff.mpr
    intro i D hi
    cases List.mem_singleton.mp (List.mem_of_getElem? hi)
    exact h

theorem ofRegion_identity (A : τ) :
    ofRegion (r := (.br 0 (.var 0) : Region Φ))
      (show ValueBranches (A :: Γ) (.br 0 (.var 0)) [A] from .br rfl (.var rfl)) = 𝟙 (ofType A) := by
  apply InducedCategory.hom_ext
  apply toHom_eq_iff.mpr
  intro i D hi
  change At [A] i D at hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    exact .native (.base (.refl (.br rfl (.var rfl))))
  | succ i => simp [At] at hi

theorem exists_region (f : ofType (Φ := Φ) (Γ := Γ) A ⟶ ofType B) :
    ∃ (r : Region Φ) (hr : ValueBranches (A :: Γ) r [B]), ofRegion hr = f := by
  obtain ⟨g, hg⟩ := Region.CfgEta.fromNative_map_surjective
    (X := ContinuationContext.single A) (Y := ContinuationContext.single B) f.hom
  obtain ⟨r, hr, he⟩ := SyntacticCategory.exists_region (Φ := Φ) (Γ := Γ) (A := A) (B := B)
    (InducedCategory.homMk g)
  refine ⟨r, hr, InducedCategory.hom_ext ?_⟩
  have h : (SyntacticCategory.ofRegion hr).hom = g := congrArg InducedCategory.Hom.hom he
  exact (congrArg (fromNative (Φ := Φ) (Γ := Γ)).map h).trans hg

set_option backward.isDefEq.respectTransparency false in
theorem iterateSum_ofRegion (hr : ValueBranches (A :: Γ) r [Silmaril.coprod B A]) :
    iterateSum (ofRegion hr) = ofRegion (SyntacticCategory.iterateRegion_valueBranches hr) := by
  apply InducedCategory.hom_ext
  change Region.CfgEta.feedback (X := ContinuationContext.single (Φ := Φ) (Γ := Γ) A)
    (Y := ContinuationContext.single B)
    (fromNative.map (ContinuationContext.singletonToHom hr) ≫
      fromNative.map (SyntacticCategory.iterationDispatchHom A B)) = _
  rw [← fromNative.map_comp, Region.CfgEta.feedback_fromNative]
  exact congrArg (fromNative (Φ := Φ) (Γ := Γ)).map
    (congrArg InducedCategory.Hom.hom (SyntacticCategory.iterate_ofRegion hr))

private theorem caseArm_subst (r : Region Φ) (a : Tm Φ) :
    ((r.renameVars (lift Nat.succ)).renameVars (lift (lift Nat.succ))).substVars
      (Tm.liftSubst (Tm.singleSubst a)) = r.renameVars (lift Nat.succ) := by
  rw [renameVars_comp, substVars_renameVars, renameVars_eq_substVars]
  congr 1
  funext i
  cases i <;> rfl

private theorem case_seq (a : Tm Φ) (r s : Region Φ) :
    (Region.br 0 a).lsubst (fun _ =>
      (Region.case (.var 0) (r.renameVars (lift Nat.succ)) (s.renameVars (lift Nat.succ))).renameVars
        (lift Nat.succ)) =
    .case a (r.renameVars (lift Nat.succ)) (s.renameVars (lift Nat.succ)) := by
  simp only [lsubst, renameVars, substVars, caseArm_subst]
  rfl

private theorem dropCapture (r : Region Φ) :
    (r.renameVars (lift Nat.succ)).substVars (Tm.singleSubst (.var 0)) = r :=
  congrFun (compLSubst_id_left (fun _ => r)) 0

set_option backward.isDefEq.respectTransparency false in
private theorem caseCopair_inl (hr : ValueBranches (A :: Γ) r [C])
    (hs : ValueBranches (B :: Γ) s [C]) :
    (sumCofan (Φ := Φ) (Γ := Γ) A B).inl ≫
      ofRegion (τ := τ) (caseValueBranches hr hs) = ofRegion (τ := τ) hr := by
  rw [sumCofan_inl (Φ := Φ) (Γ := Γ) A B]
  have hin : ValueBranches (A :: Γ) (.br 0 (.inl (.var 0)) : Region Φ) [Silmaril.coprod A B] :=
    .br rfl (.inl (.var rfl))
  apply (ofRegion_eq_iff (seqValueBranches hin (caseValueBranches hr hs)) hr).mpr
  rw [case_seq]
  have hl := ((singletonValueFamily hr).liftVars A) (ℓ := 0) (A := A) rfl
  have hr' := ((singletonValueFamily hs).liftVars A) (ℓ := 0) (A := B) rfl
  refine .native ((SubstitutionEquiv.base (.caseInl (.var (i := 0) rfl) hl.hasType hr'.hasType)).trans ?_)
  simpa only [liftLSubstVars, dropCapture] using (SubstitutionEquiv.letValue (.var (i := 0) rfl) hl.hasType)

set_option backward.isDefEq.respectTransparency false in
private theorem caseCopair_inr (hr : ValueBranches (A :: Γ) r [C])
    (hs : ValueBranches (B :: Γ) s [C]) :
    (sumCofan (Φ := Φ) (Γ := Γ) A B).inr ≫
      ofRegion (τ := τ) (caseValueBranches hr hs) = ofRegion (τ := τ) hs := by
  rw [sumCofan_inr (Φ := Φ) (Γ := Γ) A B]
  have hin : ValueBranches (B :: Γ) (.br 0 (.inr (.var 0)) : Region Φ) [Silmaril.coprod A B] :=
    .br rfl (.inr (.var rfl))
  apply (ofRegion_eq_iff (seqValueBranches hin (caseValueBranches hr hs)) hs).mpr
  rw [case_seq]
  have hl := ((singletonValueFamily hr).liftVars B) (ℓ := 0) (A := A) rfl
  have hr' := ((singletonValueFamily hs).liftVars B) (ℓ := 0) (A := B) rfl
  refine .native ((SubstitutionEquiv.base (.caseInr (.var (i := 0) rfl) hl.hasType hr'.hasType)).trans ?_)
  simpa only [liftLSubstVars, dropCapture] using (SubstitutionEquiv.letValue (.var (i := 0) rfl) hr'.hasType)

set_option backward.isDefEq.respectTransparency false in
theorem coprod_desc_ofRegion (hr : ValueBranches (A :: Γ) r [C])
    (hs : ValueBranches (B :: Γ) s [C]) :
    (sumIso A B).hom ≫ coprod.desc (ofRegion hr) (ofRegion hs) = ofRegion (caseValueBranches hr hs) := by
  apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit A B)
  · rw [← Category.assoc, sumCofan_inl_sumIso_hom (Φ := Φ) (Γ := Γ) A B, coprod.inl_desc]
    exact (caseCopair_inl hr hs).symm
  · rw [← Category.assoc, sumCofan_inr_sumIso_hom (Φ := Φ) (Γ := Γ) A B, coprod.inr_desc]
    exact (caseCopair_inr hr hs).symm

omit [TypeFormers τ] [HasTy Φ τ] in
theorem returnOrRepeat_lift {p : Region Φ} :
    (Region.case (.var 0) ((Region.br 0 (.var 0)).renameVars (lift Nat.succ))
        ((SyntacticCategory.iterateRegion A p).renameVars (lift Nat.succ))).renameVars
      (lift Nat.succ) = Region.CfgEta.returnOrRepeat A p := by
  simp only [Region.CfgEta.returnOrRepeat, renameVars, renameVars_comp]
  have h : lift (lift Nat.succ) ∘ lift Nat.succ = lift (Nat.succ ∘ Nat.succ) := by
    funext i
    cases i <;> rfl
  rw [h]
  rfl

private theorem return_valueBranches (B : τ) :
    ValueBranches (B :: Γ) (.br 0 (.var 0) : Region Φ) [B] := .br rfl (.var rfl)

theorem unrolled_valueBranches (hp : ValueBranches (A :: Γ) r [Silmaril.coprod B A]) :
    ValueBranches (A :: Γ) (r.lsubst (fun _ => Region.CfgEta.returnOrRepeat A r)) [B] := by
  have h := seqValueBranches hp
    (caseValueBranches (return_valueBranches B) (SyntacticCategory.iterateRegion_valueBranches hp))
  rw [returnOrRepeat_lift] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
theorem iterateSum_unfold_rhs (hp : ValueBranches (A :: Γ) r [Silmaril.coprod B A]) :
    ofRegion hp ≫ ((sumIso B A).hom ≫ coprod.desc (𝟙 (ofType B)) (iterateSum (ofRegion hp))) =
      ofRegion (unrolled_valueBranches hp) := by
  have hloop := SyntacticCategory.iterateRegion_valueBranches hp
  rw [iterateSum_ofRegion, ← ofRegion_identity B, coprod_desc_ofRegion]
  apply (ofRegion_eq_iff (seqValueBranches hp (caseValueBranches (return_valueBranches B) hloop))
    (unrolled_valueBranches hp)).mpr
  rw [returnOrRepeat_lift]
  exact .native (.base (.refl (unrolled_valueBranches hp).hasType))

private theorem iterateSum_fixpoint_ofRegion (hp : ValueBranches (A :: Γ) r [Silmaril.coprod B A]) :
    iterateSum (ofRegion hp) =
      ofRegion hp ≫ ((sumIso B A).hom ≫ coprod.desc (𝟙 (ofType B)) (iterateSum (ofRegion hp))) := by
  rw [iterateSum_unfold_rhs, iterateSum_ofRegion]
  exact (ofRegion_eq_iff _ _).mpr (Region.CfgEta.fixpoint hp)

set_option backward.isDefEq.respectTransparency false in
theorem iterate_fixpoint {X Y : TypeCategory Φ Γ} (f : X ⟶ Y ⨿ X) :
    iterate f = f ≫ coprod.desc (𝟙 Y) (iterate f) := by
  let A : τ := X
  let B : τ := Y
  let e := sumIso (Φ := Φ) (Γ := Γ) B A
  let step := f ≫ e.inv
  let run := iterateSum (Φ := Φ) (Γ := Γ) (A := A) (B := B)
  change run step = f ≫ coprod.desc (𝟙 Y) (run step)
  have hfix : run step = step ≫ (e.hom ≫ coprod.desc (𝟙 Y) (run step)) := by
    obtain ⟨p, hp, h⟩ := exists_region (Φ := Φ) (Γ := Γ) (A := A) (B := Silmaril.coprod B A) step
    rw [← h]
    exact iterateSum_fixpoint_ofRegion hp
  have hstep : step ≫ e.hom = f := by
    change (f ≫ e.inv) ≫ e.hom = f
    rw [Category.assoc, e.inv_hom_id]
    exact Category.comp_id f
  exact hfix.trans ((Category.assoc _ _ _).symm.trans
    (congrArg (fun g : X ⟶ Y ⨿ X => g ≫ coprod.desc (𝟙 Y) (run step)) hstep))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta
