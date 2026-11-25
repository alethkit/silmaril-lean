module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms

/-! # Assemble a categorical arrow for a typed continuation family -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ContinuationAssembly

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical.SingletonDispatcher
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (snd)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ]
  {C : Type u₂} [Category.{v₂} C] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [InstructionModel J M Φ]

local notation "inj" => labelInject
local notation "payload" => singletonLabelPayload
local notation "cut" => labelAppendSplit

theorem ofTyped {Γ : VCtx τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    (hσ : Region.LSubst.HasType Γ L K σ) :
    ∃ k, ContinuationDenotes J M (Γ := Γ) (L := L) (K := K) σ k := by
  let E := ctxObj M Γ
  induction L generalizing σ with
  | nil =>
    refine ⟨J.map (snd E (labelObj M []) ≫
      Sigma.desc (fun i : Fin (([] : List τ).length) => i.elim0)), ?_⟩
    intro i A hi
    simp [At] at hi
  | cons A L ih =>
    let head := hσ (show At (A :: L) 0 A from rfl)
    obtain ⟨tail, dtail⟩ := ih (σ := fun i => σ (i + 1)) (fun _ _ hi => hσ hi)
    let route := Isotope.LetIter.Semantics.Categorical.routeEnvironment J E (labelObj M L) (labelObj M [A])
    let branch := J.map (E ◁ payload M A) ≫ denoteRegion J M head
    refine ⟨J.map (E ◁ cut M [A] L) ≫ route ≫ coprod.desc tail branch, ?_⟩
    intro i B hi
    cases i with
    | zero =>
      cases Option.some.inj hi
      refine ⟨head, ?_⟩
      have hleg : J.map (E ◁ inj M 0 (L := A :: L) hi) ≫ J.map (E ◁ cut M [A] L) ≫
          route ≫ coprod.desc tail branch = denoteRegion J M head := by
        rw [← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp, labelAppendSplit_zero,
          MonoidalCategory.whiskerLeft_comp, J.map_comp_assoc]
        rw [← Category.assoc (J.map (E ◁ (coprod.inr : labelObj M [A] ⟶ labelObj M L ⨿ labelObj M [A]))),
          show J.map (E ◁ (coprod.inr : labelObj M [A] ⟶ labelObj M L ⨿ labelObj M [A])) ≫ route = _ from route_inr J,
          coprod.inr_desc]
        dsimp only [branch]
        rw [← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp, labelInject_payload,
          MonoidalCategory.whiskerLeft_id, J.map_id, Category.id_comp]
      simp only [MonoidalCategory.id_tensorHom]
      change RegionDenotes J M head (J.map (E ◁ inj M 0 (L := A :: L) hi) ≫
        J.map (E ◁ cut M [A] L) ≫ route ≫ coprod.desc tail branch)
      exact hleg.symm ▸ denoteRegion_spec J M head
    | succ i =>
      let ht : At L i B := hi
      obtain ⟨h, d⟩ := dtail ht
      refine ⟨h, ?_⟩
      have hleg : J.map (E ◁ inj M (i + 1) (L := A :: L) hi) ≫ J.map (E ◁ cut M [A] L) ≫
          route ≫ coprod.desc tail branch = J.map (E ◁ inj M i ht) ≫ tail := by
        rw [← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp, labelAppendSplit_succ M A ht,
          MonoidalCategory.whiskerLeft_comp, J.map_comp_assoc]
        rw [← Category.assoc (J.map (E ◁ (coprod.inl : labelObj M L ⟶ labelObj M L ⨿ labelObj M [A]))),
          show J.map (E ◁ (coprod.inl : labelObj M L ⟶ labelObj M L ⨿ labelObj M [A])) ≫ route = _ from route_inl J,
          coprod.inl_desc]
      simp only [MonoidalCategory.id_tensorHom] at d ⊢
      change RegionDenotes J M h (J.map (E ◁ inj M (i + 1) (L := A :: L) hi) ≫
        J.map (E ◁ cut M [A] L) ≫ route ≫ coprod.desc tail branch)
      exact hleg.symm ▸ d

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ContinuationAssembly
