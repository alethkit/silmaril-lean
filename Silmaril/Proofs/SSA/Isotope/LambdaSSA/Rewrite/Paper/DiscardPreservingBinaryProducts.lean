module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Discard.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Shuffle.Interchange.Thms

/-! # Construct the binary product of two types among discard-preserving values -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.DiscardPreservingBinaryProducts

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region CategoryTheory.Limits
open Paper.Extension.Singleton

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop) {ε : Type w} [HasEff Φ ε] (pe : ε)

noncomputable def discardPreservingBinaryFanIsLimit (A B : τ)
    (includeProjection : ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ},
      Paper.WithProjectionReturns.Step Γ r s L → Seed Γ r s L) :
    IsLimit (discardPreservingFan Seed pe includeProjection A B) := by
  apply discardPreservingFanIsLimit Seed pe includeProjection A B
  intro X f g hf hg
  obtain ⟨f₀, cf, ef⟩ := hf.1.2
  obtain ⟨g₀, cg, eg⟩ := hg.1.2
  refine ⟨Paper.TypeCategory.pairArrows (τ := τ) f₀ g₀, Paper.TypeCategory.centralCopies_pair cf cg, ?_⟩
  rw [map_pairArrows, ef, eg]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.DiscardPreservingBinaryProducts
