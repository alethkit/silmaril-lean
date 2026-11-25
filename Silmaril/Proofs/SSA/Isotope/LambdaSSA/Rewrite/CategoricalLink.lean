module

public import Silmaril.SSA.Isotope.LambdaSSA.LabelSubstitution.Categorical.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Thms
public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Combinators
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Labels
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.OutwardEffect
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Thms

/-! # Sequencing an exactly typed region with an effectful continuation -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (extend)
open CategoryTheory.CartesianMonoidalCategory (snd)

local notation "bindArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]

private theorem context_of_empty_hom_ext (J : V ⥤ C) [DistributiveFreydCategory J]
    {E A : V} {D : C} {f g : J.obj (E ⊗ A) ⟶ D}
    (h : (coprod.inl : A ⟶ A ⨿ A) = coprod.inr) : f = g := by
  let route := J.map (DistributiveTensor.leftIso E A A).inv ≫
    Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.splitMapCoprod J (E ⊗ A) (E ⊗ A)
  have hin : (coprod.inl : J.obj (E ⊗ A) ⟶ J.obj (E ⊗ A) ⨿ J.obj (E ⊗ A)) = coprod.inr := by
    calc
      _ = J.map (E ◁ (coprod.inl : A ⟶ A ⨿ A)) ≫ route := (distributeMap_inl J E A A).symm
      _ = J.map (E ◁ (coprod.inr : A ⟶ A ⨿ A)) ≫ route := by rw [h]
      _ = _ := distributeMap_inr J E A A
  simpa only [coprod.inl_desc, coprod.inr_desc] using congrArg (· ≫ coprod.desc f g) hin

variable [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

set_option backward.isDefEq.respectTransparency false in
private theorem link_empty {Γ : VCtx τ} {K : LCtx τ} {r : Region Φ} {σ : Nat → Region Φ}
    {hr : Region.HasType Γ r []} {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M ([] : LCtx τ))}
    (df : RegionDenotes J M hr f)
    (k : J.obj (ctxObj M Γ ⊗ labelObj M ([] : LCtx τ)) ⟶ J.obj (labelObj M K)) :
    ∃ hs : Region.HasType Γ (r.linkExits ([] : LCtx τ) σ) K, RegionDenotes J M hs (bindArrow J f k) := by
  let ρ : Ren [] K id := fun _ _ h => by simp [At] at h
  obtain ⟨he, de⟩ : ∃ he : Region.HasType Γ r K,
      RegionDenotes J M he (f ≫ J.map (labelMap M ρ)) := by
    have transport {s : Region Φ} (e : r.renameLabels id = s) :
        ∃ he : Region.HasType Γ s K, RegionDenotes J M he (f ≫ J.map (labelMap M ρ)) := by
      cases e
      exact ⟨_, df.renameLabels J M ρ⟩
    exact transport (Region.renameLabels_id r)
  have d := RegionDenotes.cfgZero (R := fun i : Fin 0 => i.elim0)
    (blocks := fun i => (σ i).renameLabels (fun j => 0 + j)) he (fun i => i.elim0) de
  have h : (coprod.inl : labelObj M ([] : LCtx τ) ⟶ labelObj M [] ⨿ labelObj M []) = coprod.inr := by
    apply Limits.Sigma.hom_ext
    exact fun i => i.elim0
  have hk : k = J.map (snd (ctxObj M Γ) (labelObj M []) ≫ labelMap M ρ) :=
    context_of_empty_hom_ext J h
  refine ⟨.cfg (fun i : Fin 0 => i.elim0) he (fun i => i.elim0), ?_⟩
  rw [hk, Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, J.map_comp, ← Category.assoc, extend_snd J (FreydCategory.CentralUnit.unit_central (J := J))]
  exact d

set_option backward.isDefEq.respectTransparency false in
private theorem link_nonempty {n : Nat} (R : Fin (n + 1) → τ)
    {Γ : VCtx τ} {K : LCtx τ} {r : Region Φ} {σ : Nat → Region Φ}
    {hr : Region.HasType Γ r (List.ofFn R)}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M (List.ofFn R))}
    (df : RegionDenotes J M hr f)
    {k : J.obj (ctxObj M Γ ⊗ labelObj M (List.ofFn R)) ⟶ J.obj (labelObj M K)}
    (hk : ContinuationDenotes J M σ k) :
    ∃ hs : Region.HasType Γ (r.linkExits (List.ofFn R) σ) K, RegionDenotes J M hs (bindArrow J f k) := by
  let E := ctxObj M Γ
  let inj (i : Fin (n + 1)) := labelInject M i (ofFnAt R i)
  choose hb db using fun i : Fin (n + 1) => hk (ofFnAt R i)
  let fromFinite : finiteLabelObj M R ⟶ labelObj M (List.ofFn R) := Limits.Sigma.desc inj
  have hinv : labelObjToFinite M R ≫ fromFinite = 𝟙 _ := by
    apply Limits.Sigma.hom_ext
    intro j
    simp only [labelObjToFinite, Limits.Sigma.ι_comp_desc_assoc, Category.assoc, fromFinite,
      finiteLabelInject, Limits.Sigma.ι_comp_desc]
    unfold inj labelInject
    simp
    exact (Category.comp_id (Limits.Sigma.ι (fun i : Fin (List.ofFn R).length => M.obj ((List.ofFn R).get i)) j)).symm
  let g := J.map (E ◁ fromFinite) ≫ k
  have hg : ∀ i, J.map (E ◁ finiteLabelInject M R i) ≫ g =
      J.map ((𝟙 E) ⊗ₘ inj i) ≫ k := by
    intro i
    dsimp only [g]
    rw [← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp, MonoidalCategory.id_tensorHom]
    congr 3
    exact Limits.Sigma.ι_comp_desc _ _
  obtain ⟨hs, ds⟩ := cfgLink_common J M (FreydCategory.CentralUnit.unit_central (J := J)) R _ hb df db g hg
  have eq : extend J f ≫ J.map (E ◁ labelObjToFinite M R) ≫ g = bindArrow J f k := by
    dsimp only [g, Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind]
    rw [← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp, hinv, MonoidalCategory.whiskerLeft_id,
      J.map_id, Category.id_comp]
  rw [eq] at ds
  have e : r.linkExits (List.ofFn R) σ =
      .cfg r (n + 1) (fun i => (σ i).renameLabels (fun j => n + 1 + j)) :=
    congrArg (fun m => Region.cfg r m (fun i => (σ i).renameLabels (fun j => m + j)))
      (List.length_ofFn (f := R))
  have transport {s : Region Φ}
      (eq : s = .cfg r (n + 1) (fun i => (σ i).renameLabels (fun j => n + 1 + j))) :
      ∃ ht : Region.HasType Γ s K, RegionDenotes J M ht (bindArrow J f k) := by
    cases eq
    exact ⟨hs, ds⟩
  exact transport e

theorem linkExits_denotes {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ} {σ : Nat → Region Φ}
    {hr : Region.HasType Γ r L} {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}
    (df : RegionDenotes J M hr f)
    {k : J.obj (ctxObj M Γ ⊗ labelObj M L) ⟶ J.obj (labelObj M K)}
    (hk : ContinuationDenotes J M σ k) :
    ∃ hs : Region.HasType Γ (r.linkExits L σ) K, RegionDenotes J M hs (bindArrow J f k) := by
  cases L with
  | nil => exact link_empty J M df k
  | cons A L =>
      let R : Fin (L.length + 1) → τ := (A :: L).get
      have transport (D : LCtx τ) (e : List.ofFn R = D)
          {ht : Region.HasType Γ r D} {g : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M D)}
          (dg : RegionDenotes J M ht g)
          {c : J.obj (ctxObj M Γ ⊗ labelObj M D) ⟶ J.obj (labelObj M K)}
          (dc : ContinuationDenotes J M σ c) :
          ∃ hs : Region.HasType Γ (r.linkExits D σ) K, RegionDenotes J M hs (bindArrow J g c) := by
        cases e
        exact link_nonempty J M R dg dc
      exact transport _ (List.ofFn_get _) df hk

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
