module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.LocalLabels.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Labels
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Combinators
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.EnvironmentNaturality

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

local notation "snd" => CartesianMonoidalCategory.snd

set_option backward.isDefEq.respectTransparency false

private theorem liftLSubstN_local {Φ : Type u₄} (n i : Nat) (h : i < n)
    (σ : Nat → Region Φ) : Region.liftLSubstN n σ i = Region.labelId i := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i =>
      rw [Region.liftLSubstN, Region.liftLSubst, ih i (by omega)]
      rfl

private theorem liftLSubstN_outward {Φ : Type u₄} (n i : Nat) (σ : Nat → Region Φ) :
    Region.liftLSubstN n σ (n + i) = (σ i).renameLabels (n + ·) := by
  induction n with
  | zero =>
    rw [show (0 + ·) = id by funext j; simp]
    simpa only [Region.liftLSubstN, Nat.zero_add] using (Region.renameLabels_id (σ i)).symm
  | succ n ih =>
    rw [show n + 1 + i = (n + i) + 1 by omega, Region.liftLSubstN, Region.liftLSubst, ih,
      Region.renameLabels_comp]
    congr 1
    funext j
    simp only [Function.comp_apply]
    omega

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)

section Restrictions

variable [DistributiveFreydCategory J]

private theorem liftLocalLabels_outward {n : Nat} (R : Fin n → τ)
    {Γ : VCtx τ} {L K : LCtx τ} {i : Nat} {A : τ} (h : At L i A)
    (k : J.obj (ctxObj M Γ ⊗ labelObj M L) ⟶ J.obj (labelObj M K)) :
    J.map (ctxObj M Γ ◁ labelInject M (n + i) (exitAt R h)) ≫
      liftLocalLabels J M (List.ofFn R) k =
    J.map (ctxObj M Γ ◁ labelInject M i h) ≫ k ≫
      J.map (labelMap M (outwardLabelRenaming (List.ofFn R) K)) := by
  unfold liftLocalLabels
  rw [← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp, labelAppendSplit_exit,
    MonoidalCategory.whiskerLeft_comp, J.map_comp_assoc, distributeMap_inl_assoc, coprod.inl_desc]

private theorem liftLocalLabels_local {n : Nat} (R : Fin n → τ)
    {Γ : VCtx τ} {L K : LCtx τ} (i : Fin n)
    (k : J.obj (ctxObj M Γ ⊗ labelObj M L) ⟶ J.obj (labelObj M K)) :
    J.map (ctxObj M Γ ◁ labelInject M i (localAt R i L)) ≫
      liftLocalLabels J M (List.ofFn R) k =
    J.map (snd (ctxObj M Γ) (M.obj (R i)) ≫ labelInject M i (localAt R i K)) := by
  unfold liftLocalLabels
  rw [← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp, labelAppendSplit_local,
    MonoidalCategory.whiskerLeft_comp, J.map_comp_assoc,
    distributeMap_inr_assoc, coprod.inr_desc, ← J.map_comp, CartesianMonoidalCategory.whiskerLeft_snd_assoc,
    labelInject_labelMap]
  rfl

end Restrictions

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

theorem continuation_liftLocalLabels {n : Nat} (R : Fin n → τ)
    {Γ : VCtx τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    {k : J.obj (ctxObj M Γ ⊗ labelObj M L) ⟶ J.obj (labelObj M K)}
    (d : ContinuationDenotes J M σ k) :
    ContinuationDenotes J M (Region.liftLSubstN n σ) (liftLocalLabels J M (List.ofFn R) k) := by
  intro i A h
  by_cases localIndex : i < n
  · let j : Fin n := ⟨i, localIndex⟩
    have hA := Option.some.inj (h.symm.trans (localAt R j L))
    subst A
    rw [liftLSubstN_local n i localIndex]
    refine ⟨.br (localAt R j K) (.var (i := 0) rfl), ?_⟩
    simp only [MonoidalCategory.id_tensorHom]
    rw [liftLocalLabels_local J M R j k, J.map_comp]
    exact .br (.var rfl)
  · obtain ⟨ℓ, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt localIndex)
    have hL : At L ℓ A := by simpa [At, List.getElem?_append_right] using h
    obtain ⟨hr, dr⟩ := d hL
    let hρ := outwardLabelRenaming (List.ofFn R) K
    have eq : Region.liftLSubstN n σ (n + ℓ) =
        (σ ℓ).renameLabels ((List.ofFn R).length + ·) := by
      simpa only [List.length_ofFn] using liftLSubstN_outward n ℓ σ
    rw [eq]
    refine ⟨hr.renameLabels hρ, ?_⟩
    simp only [MonoidalCategory.id_tensorHom]
    rw [liftLocalLabels_outward J M R hL k]
    simpa only [Category.assoc, MonoidalCategory.id_tensorHom] using dr.renameLabels J M hρ

theorem collective_continuation {n : Nat} (R : Fin n → τ)
    {Γ : VCtx τ} {L K : LCtx τ}
    {block : ∀ i, J.obj (ctxObj M (R i :: Γ)) ⟶ J.obj (labelObj M (List.ofFn R ++ L))}
    {f : J.obj (ctxObj M Γ ⊗ finiteLabelObj M R) ⟶ J.obj (labelObj M (List.ofFn R ++ L))}
    (df : CollectiveDenotes J M Γ R L block f)
    (k : J.obj (ctxObj M Γ ⊗ labelObj M (List.ofFn R ++ L)) ⟶
      J.obj (labelObj M (List.ofFn R ++ K))) :
    let E := ctxObj M Γ
    let labels := labelObj M (List.ofFn R ++ L)
    let fst := CartesianMonoidalCategory.fst
    CollectiveDenotes J M Γ R K
      (fun i => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind J (block i) (J.map (fst E (M.obj (R i)) ▷ labels) ≫ k))
      (Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind J f (J.map (fst E (finiteLabelObj M R) ▷ labels) ≫ k)) := by
  dsimp only
  constructor
  intro i
  simp only [MonoidalCategory.id_tensorHom]
  rw [← bind_pre_map, ← J.map_comp_assoc, ← MonoidalCategory.comp_whiskerRight,
    CartesianMonoidalCategory.whiskerLeft_fst]
  exact congrArg (fun f => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind J f _)
    (by simpa only [MonoidalCategory.id_tensorHom] using df.restrict i)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
