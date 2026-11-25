module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Input.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Input.Categorical.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Combinators

/-! # Denotations of packed value inputs -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

set_option backward.isDefEq.respectTransparency false

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)

section Terms

variable [DistributiveFreydCategory J] {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

theorem packedInputValue_denotes (Γ : VCtx τ) :
    Denotes J M (packedInputValue_branchValue (Φ := Φ) Γ).hasType
      (J.map (inputRecordIso M Γ).hom) := by
  induction Γ with
  | nil =>
    simpa [inputRecordIso, ctxObj, packedInputType, packedInputValue] using
      (Denotes.unit (J := J) (M := M) (Φ := Φ) (Γ := []))
  | cons A Γ ih =>
    let π := fst (ctxObj M Γ) (M.obj A)
    have dh := denotes_rename J M ih (Ren.wk Γ A) (k := π) (fun _ _ _ => rfl)
    have dnew : Denotes J M (Φ := Φ) (.var (i := 0) (rfl : At (A :: Γ) 0 A))
        (J.map (snd (ctxObj M Γ) (M.obj A))) := .var (i := 0) rfl
    have dp := Denotes.pair dh dnew
    rw [← J.map_comp, pair_map] at dp
    have hk : lift (π ≫ (inputRecordIso M Γ).hom) (snd (ctxObj M Γ) (M.obj A)) =
        (inputRecordIso M Γ).hom ▷ M.obj A := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [π]
    rw [hk, ← J.map_comp] at dp
    exact dp

private theorem denotes_left {Δ : VCtx τ} {a : Tm Φ} {A B : τ}
    {ha : Tm.HasType Δ a (Silmaril.product A B)}
    {p : ctxObj M Δ ⟶ M.obj (Silmaril.product A B)}
    (da : Denotes J M ha (J.map p)) :
    Denotes J M (.let₂ ha (.var (i := 1) rfl))
      (J.map (p ≫ (M.productIso A B).hom ≫ fst _ _)) := by
  have d := Denotes.let₂ da (Denotes.var (J := J) (M := M) (Φ := Φ)
    (i := 1) (rfl : At (B :: A :: Δ) 1 A))
  simpa only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, extend_map,
    ← J.map_comp, ctxPairIso, lookup, ctxObj, Iso.symm_hom, MonoidalCategory.id_tensorHom, Category.assoc,
    associator_inv_fst_snd, lift_whiskerLeft_assoc, lift_snd_assoc] using d

private theorem denotes_right {Δ : VCtx τ} {a : Tm Φ} {A B : τ}
    {ha : Tm.HasType Δ a (Silmaril.product A B)}
    {p : ctxObj M Δ ⟶ M.obj (Silmaril.product A B)}
    (da : Denotes J M ha (J.map p)) :
    Denotes J M (.let₂ ha (.var (i := 0) rfl))
      (J.map (p ≫ (M.productIso A B).hom ≫ snd _ _)) := by
  have d := Denotes.let₂ da (Denotes.var (J := J) (M := M) (Φ := Φ)
    (i := 0) (rfl : At (B :: A :: Δ) 0 B))
  simpa only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, extend_map,
    ← J.map_comp, ctxPairIso, lookup, ctxObj, Iso.symm_hom, MonoidalCategory.id_tensorHom, Category.assoc,
    associator_inv_snd, lift_whiskerLeft_assoc, lift_snd_assoc] using d

theorem packedInputProjection_denotes {Γ Δ : VCtx τ} {i : Nat} {A : τ} {a : Tm Φ}
    (hi : At Γ i A) {ha : Tm.HasType Δ a (packedInputType Γ)}
    {p : ctxObj M Δ ⟶ M.obj (packedInputType Γ)} (da : Denotes J M ha (J.map p)) :
    Denotes J M (packedInputProjection_hasType hi ha)
      (J.map (p ≫ (inputRecordIso M Γ).inv ≫ lookup M i hi)) := by
  induction Γ generalizing i A a with
  | nil => simp [At] at hi
  | cons B Γ ih =>
    cases i with
    | zero =>
      cases Option.some.inj hi
      simpa only [inputRecordIso, Iso.trans_inv, Iso.symm_inv, MonoidalCategory.whiskerRightIso_inv,
        lookup, Category.assoc, whiskerRight_snd] using denotes_right J M da
    | succ i =>
      simpa only [inputRecordIso, Iso.trans_inv, Iso.symm_inv, MonoidalCategory.whiskerRightIso_inv,
        lookup, Category.assoc, whiskerRight_fst_assoc] using
        ih (i := i) hi (denotes_left J M da)

end Terms

section Regions

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

theorem regionDenotes_packInputs {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    {hr : HasType Γ r L} {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}
    (d : RegionDenotes J M hr f) :
    RegionDenotes J M hr.packInputs (J.map (packedInputIso M Γ).inv ≫ f) := by
  have h : SubstDenotes J M (Φ := Φ) (fun i => packedInputProjection i (.var 0))
      (packedInputIso M Γ).inv := by
    intro i A hi
    let hvar : Tm.HasType [packedInputType Γ] (.var (Φ := Φ) 0) (packedInputType Γ) :=
      .var rfl
    refine ⟨packedInputProjection_hasType hi hvar, ?_⟩
    have dv : Denotes J M hvar (J.map (snd _ _)) := .var (i := 0) rfl
    simpa only [packedInputIso, Iso.trans_inv, Iso.symm_inv, ctxObj, leftUnitor_hom, Category.assoc] using
      packedInputProjection_denotes J M hi dv
  obtain ⟨_, hd⟩ := regionDenotes_subst J M d h
  exact hd

theorem regionDenotes_unpackInputs {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    {hr : HasType [packedInputType Γ] r L}
    {f : J.obj (ctxObj M [packedInputType Γ]) ⟶ J.obj (labelObj M L)}
    (d : RegionDenotes J M hr f) :
    RegionDenotes J M hr.unpackInputs (J.map (packedInputIso M Γ).hom ≫ f) := by
  have h : SubstDenotes J M (Tm.singleSubst (packedInputValue Γ : Tm Φ))
      (packedInputIso M Γ).hom := by
    intro i A hi
    cases i with
    | zero =>
      cases Option.some.inj hi
      refine ⟨(packedInputValue_branchValue (Φ := Φ) Γ).hasType, ?_⟩
      simpa only [packedInputIso, Iso.trans_hom, Iso.symm_hom, lookup, ctxObj, Category.assoc,
        leftUnitor_inv_snd, Category.comp_id] using packedInputValue_denotes (Φ := Φ) J M Γ
    | succ i => simp [At] at hi
  obtain ⟨_, hd⟩ := regionDenotes_subst J M d h
  exact hd

end Regions

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
