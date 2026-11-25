module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.BinaryLetBind.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.BinaryLetBind

/-! # Soundness of the standalone binary-let binding step -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.BinaryLetBind

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits

universe u v u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

variable {s : Region Φ}

/-- Both endpoints carry the same structural denotation, for any exactly
typed scrutinee and body. -/
theorem Step.denotes (h : Step Γ r s L) :
    ∃ f, RegionDenotes J M h.typed.1 f ∧ RegionDenotes J M h.typed.2 f :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.BinaryLetBind.step_denotes J M h

/-- Coherent models agree on the chosen arrows of the two endpoints. -/
theorem Step.sound [RegionTypingCoherent (Φ := Φ) J M] (h : Step Γ r s L)
    (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs := by
  obtain ⟨_, dr, ds⟩ := h.denotes J M
  exact (RegionDenotes.eq_denote (h := hr) J M dr).symm.trans
    (RegionDenotes.eq_denote (h := hs) J M ds)

end Silmaril.Isotope.LambdaSSA.Region.BinaryLetBind
