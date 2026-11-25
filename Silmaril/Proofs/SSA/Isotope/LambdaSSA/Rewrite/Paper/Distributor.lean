module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Coproducts.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Constructors.Thms

/-! # Distributor computations in the Paper singleton quotient -/

public section

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory
open CfgEta.TypeCategory (whiskerLeftRegion whiskerLeftRegion_typed seqValueBranches caseValueBranches)
open Paper.RetainedLet (unpackBody_typed)
open Paper.RetainedCase (packedArms_typed boundCase routeCase_ofRegion)
open CfgEta.TypeCategory.Retained (distributorRegion distributorRegion_typed)

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Distributor

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {X A B : τ}

private abbrev productInl (X A B : τ) :
    ValueBranches [Silmaril.product X A] (.br 0 (.inl (.var 0)) : Region Φ)
      [Silmaril.coprod (Silmaril.product X A) (Silmaril.product X B)] :=
  .br rfl (.inl (.var (i := 0) rfl))

private abbrev productInr (X A B : τ) :
    ValueBranches [Silmaril.product X B] (.br 0 (.inr (.var 0)) : Region Φ)
      [Silmaril.coprod (Silmaril.product X A) (Silmaril.product X B)] :=
  .br rfl (.inr (.var (i := 0) rfl))

set_option backward.isDefEq.respectTransparency false in
theorem left_distributor_inl (X A B : τ) :
    whiskerLeft (τ := τ) (ofType (Φ := Φ) X) (sumCofan (Φ := Φ) A B).inl ≫
      ofRegion (τ := τ) (distributorRegion_typed X A B) =
        (sumCofan (Φ := Φ) (Silmaril.product X A) (Silmaril.product X B)).inl := by
  let P := Silmaril.product X A
  let Q := Silmaril.product X B
  let L : LCtx τ := [Silmaril.coprod P Q]
  let C : VCtx τ := [A, X, P]
  let left : Region Φ := .br 0 (.inl (.pair (.var 2) (.var 0)))
  let right : Region Φ := .br 0 (.inr (.pair (.var 2) (.var 0)))
  have hL : HasType (A :: C) left L :=
    .br (rfl : At L 0 (Silmaril.coprod P Q))
      (.inl (B := Q) (.pair (.var (i := 2) (rfl : At (A :: C) 2 X)) (.var (i := 0) rfl)))
  have hR : HasType (B :: C) right L :=
    .br (rfl : At L 0 (Silmaril.coprod P Q))
      (.inr (A := P) (.pair (.var (i := 2) (rfl : At (B :: C) 2 X)) (.var (i := 0) rfl)))
  have hbody : HasType (Silmaril.coprod A B :: X :: C) (.case (.var 0) left right) L :=
    .case (.var (i := 0) rfl)
      (.br (rfl : At L 0 (Silmaril.coprod P Q))
        (.inl (B := Q) (.pair (.var (i := 2) (rfl : At (A :: Silmaril.coprod A B :: X :: C) 2 X))
          (.var (i := 0) rfl))))
      (.br (rfl : At L 0 (Silmaril.coprod P Q))
        (.inr (A := P) (.pair (.var (i := 2) (rfl : At (B :: Silmaril.coprod A B :: X :: C) 2 X))
          (.var (i := 0) rfl))))
  have e : Paper.Eqv C (.let₂ (.pair (.var 1) (.inl (.var 0))) (.case (.var 0) left right))
      (.case (.inl (.var 0)) left right) L := by
    have step := Paper.Eqv.productBeta (.let₂Beta (.var (i := 1) (rfl : At C 1 X))
      (.inl (B := B) (.var (i := 0) (rfl : At C 0 A))) hbody)
    exact step
  have beta : Paper.Eqv C (.case (.inl (.var 0)) left right)
      (.br 0 (.inl (.pair (.var 1) (.var 0)))) L :=
    .cfgEta (.native ((SubstitutionEquiv.base (.caseInl (.var (i := 0) rfl) hL hR)).trans
      (.letValue (.var (i := 0) rfl) hL)))
  let rawInl : ValueBranches [A] (.br 0 (.inl (.var 0)) : Region Φ) [Silmaril.coprod A B] :=
    .br rfl (.inl (.var (i := 0) rfl))
  let rawId : ValueBranches [A] (.br 0 (.var 0) : Region Φ) [A] :=
    .br rfl (.var (i := 0) rfl)
  rw [sumCofan_inl (Φ := Φ) A B, whiskerLeft_ofRegion X rawInl,
    ofRegion_comp _ _ (seqValueBranches (whiskerLeftRegion_typed X rawInl) (distributorRegion_typed X A B))]
  calc
    _ = ofRegion (seqValueBranches (whiskerLeftRegion_typed X rawId) (productInl (Φ := Φ) X A B)) :=
      (ofRegion_eq_iff _ _).2 (.let₂ (.var (i := 0) rfl) (e.trans beta))
    _ = _ := by
      rw [← ofRegion_comp (whiskerLeftRegion_typed X rawId) (productInl X A B),
        ← whiskerLeft_ofRegion X rawId, ofRegion_id, whiskerLeft_id]
      change 𝟙 (ofType P) ≫ ofRegion (productInl X A B) = _
      rw [Category.id_comp]
      exact (sumCofan_inl (Φ := Φ) P Q).symm

set_option backward.isDefEq.respectTransparency false in
theorem left_distributor_inr (X A B : τ) :
    whiskerLeft (τ := τ) (ofType (Φ := Φ) X) (sumCofan (Φ := Φ) A B).inr ≫
      ofRegion (τ := τ) (distributorRegion_typed X A B) =
        (sumCofan (Φ := Φ) (Silmaril.product X A) (Silmaril.product X B)).inr := by
  let P := Silmaril.product X A
  let Q := Silmaril.product X B
  let L : LCtx τ := [Silmaril.coprod P Q]
  let C : VCtx τ := [B, X, Q]
  let left : Region Φ := .br 0 (.inl (.pair (.var 2) (.var 0)))
  let right : Region Φ := .br 0 (.inr (.pair (.var 2) (.var 0)))
  have hL : HasType (A :: C) left L :=
    .br (rfl : At L 0 (Silmaril.coprod P Q))
      (.inl (B := Q) (.pair (.var (i := 2) (rfl : At (A :: C) 2 X)) (.var (i := 0) rfl)))
  have hR : HasType (B :: C) right L :=
    .br (rfl : At L 0 (Silmaril.coprod P Q))
      (.inr (A := P) (.pair (.var (i := 2) (rfl : At (B :: C) 2 X)) (.var (i := 0) rfl)))
  have hbody : HasType (Silmaril.coprod A B :: X :: C) (.case (.var 0) left right) L :=
    .case (.var (i := 0) rfl)
      (.br (rfl : At L 0 (Silmaril.coprod P Q))
        (.inl (B := Q) (.pair (.var (i := 2) (rfl : At (A :: Silmaril.coprod A B :: X :: C) 2 X))
          (.var (i := 0) rfl))))
      (.br (rfl : At L 0 (Silmaril.coprod P Q))
        (.inr (A := P) (.pair (.var (i := 2) (rfl : At (B :: Silmaril.coprod A B :: X :: C) 2 X))
          (.var (i := 0) rfl))))
  have e : Paper.Eqv C (.let₂ (.pair (.var 1) (.inr (.var 0))) (.case (.var 0) left right))
      (.case (.inr (.var 0)) left right) L := by
    have step := Paper.Eqv.productBeta (.let₂Beta (.var (i := 1) (rfl : At C 1 X))
      (.inr (A := A) (.var (i := 0) (rfl : At C 0 B))) hbody)
    exact step
  have beta : Paper.Eqv C (.case (.inr (.var 0)) left right)
      (.br 0 (.inr (.pair (.var 1) (.var 0)))) L :=
    .cfgEta (.native ((SubstitutionEquiv.base (.caseInr (.var (i := 0) rfl) hL hR)).trans
      (.letValue (.var (i := 0) rfl) hR)))
  let rawInr : ValueBranches [B] (.br 0 (.inr (.var 0)) : Region Φ) [Silmaril.coprod A B] :=
    .br rfl (.inr (.var (i := 0) rfl))
  let rawId : ValueBranches [B] (.br 0 (.var 0) : Region Φ) [B] :=
    .br rfl (.var (i := 0) rfl)
  rw [sumCofan_inr (Φ := Φ) A B, whiskerLeft_ofRegion X rawInr,
    ofRegion_comp _ _ (seqValueBranches (whiskerLeftRegion_typed X rawInr) (distributorRegion_typed X A B))]
  calc
    _ = ofRegion (seqValueBranches (whiskerLeftRegion_typed X rawId) (productInr (Φ := Φ) X A B)) :=
      (ofRegion_eq_iff _ _).2 (.let₂ (.var (i := 0) rfl) (e.trans beta))
    _ = _ := by
      rw [← ofRegion_comp (whiskerLeftRegion_typed X rawId) (productInr X A B),
        ← whiskerLeft_ofRegion X rawId, ofRegion_id, whiskerLeft_id]
      change 𝟙 (ofType Q) ≫ ofRegion (productInr X A B) = _
      rw [Category.id_comp]
      exact (sumCofan_inr (Φ := Φ) P Q).symm

set_option backward.isDefEq.respectTransparency false in
theorem case_ofRegion_inl {D : τ} {p q : Region Φ} (hp : ValueBranches [A] p [D])
    (hq : ValueBranches [B] q [D]) :
    (sumCofan (Φ := Φ) A B).inl ≫ ofRegion (τ := τ) (caseValueBranches hp hq) = ofRegion (τ := τ) hp := by
  let hi : ValueBranches [A] (.br 0 (.inl (.var 0)) : Region Φ) [Silmaril.coprod A B] :=
    .br rfl (.inl (.var (i := 0) rfl))
  let hseq := seqValueBranches hi (caseValueBranches hp hq)
  rw [sumCofan_inl, ofRegion_comp hi (caseValueBranches hp hq) hseq]
  apply (ofRegion_eq_iff _ _).2
  apply Paper.Eqv.cfgEta
  apply (CfgEta.TypeCategory.ofRegion_eq_iff hseq hp).1
  rw [← CfgEta.TypeCategory.ofRegion_comp hi (caseValueBranches hp hq), ← CfgEta.TypeCategory.sumCofan_inl,
    ← CfgEta.TypeCategory.coprod_desc_ofRegion hp hq, ← Category.assoc,
    CfgEta.TypeCategory.sumCofan_inl_sumIso_hom, coprod.inl_desc]

set_option backward.isDefEq.respectTransparency false in
theorem case_ofRegion_inr {D : τ} {p q : Region Φ} (hp : ValueBranches [A] p [D])
    (hq : ValueBranches [B] q [D]) :
    (sumCofan (Φ := Φ) A B).inr ≫ ofRegion (τ := τ) (caseValueBranches hp hq) = ofRegion (τ := τ) hq := by
  let hi : ValueBranches [B] (.br 0 (.inr (.var 0)) : Region Φ) [Silmaril.coprod A B] :=
    .br rfl (.inr (.var (i := 0) rfl))
  let hseq := seqValueBranches hi (caseValueBranches hp hq)
  rw [sumCofan_inr, ofRegion_comp hi (caseValueBranches hp hq) hseq]
  apply (ofRegion_eq_iff _ _).2
  apply Paper.Eqv.cfgEta
  apply (CfgEta.TypeCategory.ofRegion_eq_iff hseq hq).1
  rw [← CfgEta.TypeCategory.ofRegion_comp hi (caseValueBranches hp hq), ← CfgEta.TypeCategory.sumCofan_inr,
    ← CfgEta.TypeCategory.coprod_desc_ofRegion hp hq, ← Category.assoc,
    CfgEta.TypeCategory.sumCofan_inr_sumIso_hom, coprod.inr_desc]

set_option backward.isDefEq.respectTransparency false in
noncomputable def distributorIso (X A B : τ) :
    ofType (Φ := Φ) (Silmaril.product X (Silmaril.coprod A B)) ≅
      ofType (Silmaril.coprod (Silmaril.product X A) (Silmaril.product X B)) := by
  let S := Silmaril.coprod A B
  let P := Silmaril.product X A
  let Q := Silmaril.product X B
  let T := Silmaril.product X S
  let hl : ValueBranches [A, X] (.br 0 (.pair (.var 1) (.inl (.var 0))) : Region Φ) [T] :=
    .br rfl (.pair (.var (i := 1) rfl) (.inl (.var (i := 0) rfl)))
  let hr : ValueBranches [B, X] (.br 0 (.pair (.var 1) (.inr (.var 0))) : Region Φ) [T] :=
    .br rfl (.pair (.var (i := 1) rfl) (.inr (.var (i := 0) rfl)))
  refine ⟨ofRegion (distributorRegion_typed X A B), ofRegion (packedArms_typed hl hr), ?_, ?_⟩
  · rw [routeCase_ofRegion hl hr, ← ofRegion_id (Φ := Φ) T]
    apply (ofRegion_eq_iff _ _).2
    have etaBody : HasType [S, S, X] (.br 0 (.pair (.var 2) (.var 0)) : Region Φ) [T] :=
      .br rfl (.pair (.var (i := 2) rfl) (.var (i := 0) rfl))
    have e : Paper.Eqv [S, X]
        (boundCase (.br 0 (.pair (.var 1) (.inl (.var 0)))) (.br 0 (.pair (.var 1) (.inr (.var 0)))))
        (.br 0 (.pair (.var 1) (.var 0))) [T] :=
      .cfgEta (.native (.caseValue (.var (i := 0) (rfl : At [S, X] 0 S)) etaBody))
    have lifted := e.renameVars (((Ren.wk ([] : VCtx τ) T).lift X).lift S)
    exact (Paper.Eqv.let₂ (.var (i := 0) (rfl : At [T] 0 T)) lifted).trans
      (.productEta (.let₂Eta rfl rfl))
  · apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit P Q)
    · change (sumCofan (Φ := Φ) P Q).inl ≫ _ ≫ _ = (sumCofan (Φ := Φ) P Q).inl ≫ 𝟙 (ofType (Silmaril.coprod P Q))
      rw [← Category.assoc, case_ofRegion_inl (unpackBody_typed hl) (unpackBody_typed hr)]
      have hb : ofRegion (unpackBody_typed hl) =
          whiskerLeft (ofType (Φ := Φ) X) (sumCofan (Φ := Φ) A B).inl := by
        rw [sumCofan_inl, whiskerLeft_ofRegion]
      rw [hb, left_distributor_inl]
      exact (Category.comp_id _).symm
    · change (sumCofan (Φ := Φ) P Q).inr ≫ _ ≫ _ = (sumCofan (Φ := Φ) P Q).inr ≫ 𝟙 (ofType (Silmaril.coprod P Q))
      rw [← Category.assoc, case_ofRegion_inr (unpackBody_typed hl) (unpackBody_typed hr)]
      have hb : ofRegion (unpackBody_typed hr) =
          whiskerLeft (ofType (Φ := Φ) X) (sumCofan (Φ := Φ) A B).inr := by
        rw [sumCofan_inr, whiskerLeft_ofRegion]
      rw [hb, left_distributor_inr]
      exact (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
theorem distributor_hom_ext {D : τ} {X A B : τ}
    {f g : ofType (Φ := Φ) (Silmaril.product X (Silmaril.coprod A B)) ⟶ ofType D}
    (hl : whiskerLeft (ofType X) (sumCofan (Φ := Φ) A B).inl ≫ f =
      whiskerLeft (ofType X) (sumCofan (Φ := Φ) A B).inl ≫ g)
    (hr : whiskerLeft (ofType X) (sumCofan (Φ := Φ) A B).inr ≫ f =
      whiskerLeft (ofType X) (sumCofan (Φ := Φ) A B).inr ≫ g) : f = g := by
  let e := distributorIso (Φ := Φ) X A B
  apply (cancel_epi e.inv).1
  apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit _ _)
  · have hin : whiskerLeft (ofType X) (sumCofan (Φ := Φ) A B).inl ≫ e.hom =
        (sumCofan (Φ := Φ) (Silmaril.product X A) (Silmaril.product X B)).inl :=
      left_distributor_inl X A B
    simp only [← hin, Category.assoc, Iso.hom_inv_id_assoc]
    exact hl
  · have hin : whiskerLeft (ofType X) (sumCofan (Φ := Φ) A B).inr ≫ e.hom =
        (sumCofan (Φ := Φ) (Silmaril.product X A) (Silmaril.product X B)).inr :=
      left_distributor_inr X A B
    simp only [← hin, Category.assoc, Iso.hom_inv_id_assoc]
    exact hr

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Distributor

