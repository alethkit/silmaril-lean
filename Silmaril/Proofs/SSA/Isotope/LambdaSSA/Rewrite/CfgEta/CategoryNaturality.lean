module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Naturality.Defs

/-! # Naturality of iteration in the CFG η quotient -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Region.CfgEta (TypeCategory fromNative prepend)
open Region.CfgEta.TypeCategory
open Region.ContinuationContext (single sumTag)
open Region.SyntacticCategory (iterationDispatchHom)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}
  {A B C : τ}

set_option backward.isDefEq.respectTransparency false in
private theorem native_dispatch_inl (A B : τ) :
    ((single (Φ := Φ) (Γ := Γ) B).appendInl (single A) ≫ sumTag B A) ≫
      iterationDispatchHom A B = (single A).appendInr (single B) := by
  rw [ContinuationContext.appendInl_sumTag]
  apply ContinuationFamily.toHom_eq_iff.mpr
  intro i D hi
  change At [B] i D at hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    have hl : HasType (B :: B :: Γ) (.br 1 (.var 0) : Region Φ) [A, B] := .br rfl (.var rfl)
    have hr : HasType (A :: B :: Γ) (.br 0 (.var 0) : Region Φ) [A, B] := .br rfl (.var rfl)
    exact (SubstitutionEquiv.base (.caseInl (.var (i := 0) rfl) hl hr)).trans
      (.letValue (.var (i := 0) rfl) hl)
  | succ i => simp [At] at hi

set_option backward.isDefEq.respectTransparency false in
private theorem native_dispatch_inr (A B : τ) :
    ((single (Φ := Φ) (Γ := Γ) B).appendInr (single A) ≫ sumTag B A) ≫
      iterationDispatchHom A B = (single A).appendInl (single B) := by
  rw [ContinuationContext.appendInr_sumTag]
  apply ContinuationFamily.toHom_eq_iff.mpr
  intro i D hi
  change At [A] i D at hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    have hl : HasType (B :: A :: Γ) (.br 1 (.var 0) : Region Φ) [A, B] := .br rfl (.var rfl)
    have hr : HasType (A :: A :: Γ) (.br 0 (.var 0) : Region Φ) [A, B] := .br rfl (.var rfl)
    exact (SubstitutionEquiv.base (.caseInr (.var (i := 0) rfl) hl hr)).trans
      (.letValue (.var (i := 0) rfl) hr)
  | succ i => simp [At] at hi

@[reassoc]
theorem dispatch_inl (A B : τ) :
    (sumCofan (Φ := Φ) (Γ := Γ) B A).inl.hom ≫ fromNative.map (iterationDispatchHom A B) =
      fromNative.map ((single A).appendInr (single B)) :=
  (fromNative.map_comp _ _).symm.trans
    (congrArg (fromNative (Φ := Φ) (Γ := Γ)).map (native_dispatch_inl (Φ := Φ) (Γ := Γ) A B))

@[reassoc]
theorem dispatch_inr (A B : τ) :
    (sumCofan (Φ := Φ) (Γ := Γ) B A).inr.hom ≫ fromNative.map (iterationDispatchHom A B) =
      fromNative.map ((single A).appendInl (single B)) :=
  (fromNative.map_comp _ _).symm.trans
    (congrArg (fromNative (Φ := Φ) (Γ := Γ)).map (native_dispatch_inr (Φ := Φ) (Γ := Γ) A B))

set_option backward.isDefEq.respectTransparency false in
private theorem mapReturn_inl (g : ofType (Φ := Φ) (Γ := Γ) B ⟶ ofType C) :
    (sumCofan (Φ := Φ) (Γ := Γ) B A).inl ≫ mapReturn A g =
      g ≫ (sumCofan (Φ := Φ) (Γ := Γ) C A).inl := by
  have hi : coprod.inl ≫ (sumIso (Φ := Φ) (Γ := Γ) C A).inv = (sumCofan C A).inl := by
    rw [← sumCofan_inl_sumIso_hom (Φ := Φ) (Γ := Γ) C A, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [mapReturn, ← Category.assoc, sumCofan_inl_sumIso_hom (Φ := Φ) (Γ := Γ) B A,
    coprod.inl_map_assoc, hi]

set_option backward.isDefEq.respectTransparency false in
private theorem mapReturn_inr (g : ofType (Φ := Φ) (Γ := Γ) B ⟶ ofType C) :
    (sumCofan (Φ := Φ) (Γ := Γ) B A).inr ≫ mapReturn A g =
      (sumCofan (Φ := Φ) (Γ := Γ) C A).inr := by
  have hi : coprod.inr ≫ (sumIso (Φ := Φ) (Γ := Γ) C A).inv = (sumCofan C A).inr := by
    rw [← sumCofan_inr_sumIso_hom (Φ := Φ) (Γ := Γ) C A, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [mapReturn, ← Category.assoc, sumCofan_inr_sumIso_hom (Φ := Φ) (Γ := Γ) B A,
    coprod.inr_map_assoc, Category.id_comp, hi]

set_option backward.isDefEq.respectTransparency false in
private theorem mapReturn_dispatch (g : ofType (Φ := Φ) (Γ := Γ) B ⟶ ofType C) :
    (mapReturn A g).hom ≫ fromNative.map (iterationDispatchHom A C) =
      fromNative.map (iterationDispatchHom A B) ≫ prepend (single A) g.hom := by
  have hl := congrArg InducedCategory.Hom.hom (mapReturn_inl (A := A) g)
  have hr := congrArg InducedCategory.Hom.hom (mapReturn_inr (A := A) g)
  change (sumCofan B A).inl.hom ≫ (mapReturn A g).hom = g.hom ≫ (sumCofan C A).inl.hom at hl
  change (sumCofan B A).inr.hom ≫ (mapReturn A g).hom = (sumCofan C A).inr.hom at hr
  apply BinaryCofan.IsColimit.hom_ext (Region.CfgEta.singletonSumIsColimit B A)
  · change (sumCofan B A).inl.hom ≫ _ = (sumCofan B A).inl.hom ≫ _
    rw [← Category.assoc, hl, Category.assoc, dispatch_inl, dispatch_inl_assoc,
      Region.CfgEta.appendInr_prepend]
    rfl
  · change (sumCofan B A).inr.hom ≫ _ = (sumCofan B A).inr.hom ≫ _
    rw [← Category.assoc, hr, dispatch_inr, dispatch_inr_assoc, Region.CfgEta.appendInl_prepend]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem iterateSum_naturality
    (f : ofType (Φ := Φ) (Γ := Γ) A ⟶ ofType (Silmaril.coprod B A))
    (g : ofType (Φ := Φ) (Γ := Γ) B ⟶ ofType C) :
    iterateSum f ≫ g = iterateSum (f ≫ mapReturn A g) := by
  apply InducedCategory.hom_ext
  change Region.CfgEta.feedback (X := single A) (Y := single B)
      (f.hom ≫ fromNative.map (iterationDispatchHom A B)) ≫ g.hom =
    Region.CfgEta.feedback (X := single A) (Y := single C)
      ((f.hom ≫ (mapReturn A g).hom) ≫ fromNative.map (iterationDispatchHom A C))
  rw [Region.CfgEta.feedback_postcompose]
  simp only [Category.assoc, mapReturn_dispatch]

set_option backward.isDefEq.respectTransparency false in
theorem iterate_naturality {X Y Z : TypeCategory Φ Γ} (f : X ⟶ Y ⨿ X) (g : Y ⟶ Z) :
    iterate f ≫ g = iterate (f ≫ coprod.map g (𝟙 X)) := by
  let A : τ := X
  let B : τ := Y
  let C : τ := Z
  let e := sumIso (Φ := Φ) (Γ := Γ) B A
  let e' := sumIso (Φ := Φ) (Γ := Γ) C A
  have h := iterateSum_naturality (Φ := Φ) (Γ := Γ) (A := A) (B := B) (C := C) (f ≫ e.inv) g
  have hmap : (f ≫ e.inv) ≫ mapReturn (Φ := Φ) (Γ := Γ) A g =
      (f ≫ coprod.map g (𝟙 X)) ≫ e'.inv := by
    change (f ≫ e.inv) ≫ e.hom ≫ coprod.map g (𝟙 X) ≫ e'.inv = _
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hmap] at h
  exact h

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta
