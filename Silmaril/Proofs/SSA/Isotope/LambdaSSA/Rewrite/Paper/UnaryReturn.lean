module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.ReturnFusion.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.BranchNormalization.Thms

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnaryReturn

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open Silmaril.Isotope.LambdaSSA.Region.Paper.UnaryReturn
open CfgEta.TypeCategory (returnRegion returnRegion_typed)
open RetainedLet (returnOnce)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
variable {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} {D : τ} {t : Tm Φ}
variable {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}

theorem returnRegion_eq_returnOnce
    (includeStep : ∀ {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}, Step Γ r s L → Seed Γ r s L)
    (ht : Tm.HasType Γ t D) :
    Extension.Eqv Seed Γ (returnRegion t) (returnOnce t) [D] := by
  induction t generalizing Γ D with
  | let₁ a b iha ihb =>
    cases ht with
    | @let₁ Γ _ _ A D ha hb =>
      have maps : LSubst.HasType Γ [A] [D] (fun _ => returnRegion b) := by
        intro i X hi
        cases i with
        | zero =>
          cases Option.some.inj hi
          exact (returnRegion_typed hb).hasType
        | succ i => simp [At] at hi
      have h := Extension.Eqv.lsubstPost (iha ha) (returnRegion_typed ha) (returnOnce_valueBranches ha) maps
      change Extension.Eqv Seed Γ (returnRegion (.let₁ a b))
        ((Region.br 0 a).bindBranchArguments.lsubst (fun _ => returnRegion b)) [D] at h
      rw [lsubst_bindBranchArguments_br] at h
      have e := Step.fuse ha hb
      exact h.trans ((Extension.Eqv.let₁ ha (ihb hb)).trans (.extra e.typed.1 e.typed.2 (includeStep e)))
  | _ => exact .refl (returnOnce_valueBranches ht).hasType

section Soundness

open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (bind duplicate)
open scoped MonoidalCategory

universe u₁ u₂ v₁ v₂

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

theorem step_denotes (e : Step Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    ∃ f, RegionDenotes J M hr f ∧ RegionDenotes J M hs f := by
  cases e with
  | @fuse A D a b ha hb =>
    let i : At [D] 0 D := rfl
    let rawB := HasType.br (ℓ := 0) i hb
    let rawLet := HasType.br (ℓ := 0) i (.let₁ ha hb)
    let da := denote_spec J M ha
    let db := denote_spec J M hb
    have normB := denoteRegion_bindBranchArguments J M
      (FreydCategory.CentralUnit.unit_central (J := J)) rawB
    have normLet := denoteRegion_bindBranchArguments J M
      (FreydCategory.CentralUnit.unit_central (J := J)) rawLet
    have denB := RegionDenotes.br (h := i) db
    have denLet := RegionDenotes.br (h := i) (Denotes.let₁ da db)
    have leftBody : RegionDenotes J M rawB.bindBranchArguments.hasType
        (denote J M hb ≫ J.map (labelInject M 0 i)) :=
      (((RegionDenotes.eq_denote J M denB).trans normB).symm) ▸
        denoteRegion_spec J M rawB.bindBranchArguments.hasType
    have left := RegionDenotes.let₁ da leftBody
    have right : RegionDenotes J M rawLet.bindBranchArguments.hasType
        (bind J (denote J M ha) (denote J M hb) ≫ J.map (labelInject M 0 i)) :=
      (((RegionDenotes.eq_denote J M denLet).trans normLet).symm) ▸
        denoteRegion_spec J M rawLet.bindBranchArguments.hasType
    refine ⟨_, left, ?_⟩
    have assoc :
        bind J (denote J M ha) (denote J M hb) ≫ J.map (labelInject M 0 i) =
          bind J (denote J M ha) (denote J M hb ≫ J.map (labelInject M 0 i)) := by
      unfold Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
      exact Category.assoc _ _ _
    exact assoc ▸ right

end Soundness

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnaryReturn
