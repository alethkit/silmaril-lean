module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.BinaryLetBind.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution

/-! # Denotational validity of binary-let scope reordering -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.BinaryLetBind

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift)
open Silmaril.Isotope.LambdaSSA.Region.BinaryLetBind

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {A B : τ}
  {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ} {a : Tm Φ}

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory (fst snd whiskerRight_snd whiskerRight_fst_assoc)
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel extend_map)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite (SubstDenotes regionDenotes_subst)

universe u₁ u₂ v₁ v₂

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

set_option backward.isDefEq.respectTransparency false in
private theorem weaken_under_pair {P : τ} (hr : Region.HasType (B :: A :: Γ) r L)
    {f : J.obj (ctxObj M (B :: A :: Γ)) ⟶ J.obj (labelObj M L)} (d : RegionDenotes J M hr f) :
    RegionDenotes J M (hr.renameVars (((Ren.wk Γ P).lift A).lift B))
      (J.map (((fst (ctxObj M Γ) (M.obj P)) ▷ M.obj A) ▷ M.obj B) ≫ f) := by
  let ρ := ((Ren.wk Γ P).lift A).lift B
  let k := ((fst (ctxObj M Γ) (M.obj P)) ▷ M.obj A) ▷ M.obj B
  have hσ : SubstDenotes (Φ := Φ) J M (Γ := B :: A :: Γ) (Δ := B :: A :: P :: Γ)
      (Tm.var ∘ (lift (lift Nat.succ))) k := by
    intro i T hi
    refine ⟨.var (ρ hi), ?_⟩
    have e : k ≫ lookup M i hi = lookup M (lift (lift Nat.succ) i) (ρ hi) := by
      cases i with
      | zero =>
        cases Option.some.inj hi
        simp only [k, lookup, lift, ctxObj, whiskerRight_snd]
      | succ i =>
        cases i with
        | zero =>
          cases Option.some.inj hi
          simp only [k, lookup, lift, ctxObj, whiskerRight_fst_assoc, whiskerRight_snd]
        | succ i =>
          simp only [k, lookup, lift, ctxObj, whiskerRight_fst_assoc]
    rw [e]
    exact .var (ρ hi)
  obtain ⟨_, dr⟩ := regionDenotes_subst J M d hσ
  simpa only [← Region.renameVars_eq_substVars] using dr

omit [SymmetricCategory V] [HasFiniteCoproducts V] [DistributiveTensor V] in
private theorem pure_scope (E P A B : V) (m : P ⟶ A ⊗ B) :
    CartesianMonoidalCategory.lift (𝟙 (E ⊗ P)) (snd E P) ≫ ((E ⊗ P) ◁ m) ≫
      (α_ (E ⊗ P) A B).inv ≫ ((fst E P) ▷ A) ▷ B = (E ◁ m) ≫ (α_ E A B).inv := by
  rw [← MonoidalCategory.associator_inv_naturality_left,
    MonoidalCategory.whisker_exchange_assoc (fst E P) m, CartesianMonoidalCategory.lift_whiskerRight_assoc,
    Category.id_comp, CartesianMonoidalCategory.lift_fst_snd, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem rebind_denotes (ha : Tm.HasType Γ a (Silmaril.product A B))
    (hr : Region.HasType (B :: A :: Γ) r L)
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj (Silmaril.product A B))}
    {g : J.obj (ctxObj M (B :: A :: Γ)) ⟶ J.obj (labelObj M L)}
    (da : Denotes J M ha f) (dr : RegionDenotes J M hr g) :
    RegionDenotes J M (rebound_typed ha hr)
      (Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind J f
        (J.map ((𝟙 _) ⊗ₘ (M.productIso A B).hom) ≫
          J.map (ctxPairIso M Γ A B).hom ≫ g)) := by
  let P := Silmaril.product A B
  have dv := Denotes.var (J := J) (M := M) (Φ := Φ) (i := 0) (rfl : At (P :: Γ) 0 P)
  have dw := weaken_under_pair (P := P) J M hr dr
  have h := RegionDenotes.let₁ da (.let₂ dv dw)
  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
    lookup, extend_map, ← J.map_comp_assoc, MonoidalCategory.id_tensorHom,
    ctxPairIso, Iso.symm_hom, ctxObj] at h ⊢
  rw [pure_scope] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
theorem step_denotes {s : Region Φ} (h : Step Γ r s L) :
    ∃ f, RegionDenotes J M h.typed.1 f ∧ RegionDenotes J M h.typed.2 f := by
  cases h with
  | bind ha hr =>
    let da := denote_spec J M ha
    let dr := denoteRegion_spec J M hr
    exact ⟨_, .let₂ da dr, rebind_denotes J M ha hr da dr⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.BinaryLetBind
