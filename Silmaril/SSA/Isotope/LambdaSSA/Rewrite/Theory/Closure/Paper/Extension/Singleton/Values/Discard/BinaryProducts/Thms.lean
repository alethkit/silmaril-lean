module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Discard.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.DiscardPreservingBinaryProducts

/-! # Binary products of discard-preserving projected copying values -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region CategoryTheory.Limits

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop) {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- The chosen projection fan is limiting for every pair of types in the discard-preserving
value category as soon as the extension includes the guarded projection-return rules. -/
noncomputable def discardPreservingBinaryFanIsLimit (A B : τ)
    (includeProjection : ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ},
      Paper.WithProjectionReturns.Step Γ r s L → Seed Γ r s L) :
    IsLimit (discardPreservingFan Seed pe includeProjection A B) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.DiscardPreservingBinaryProducts.discardPreservingBinaryFanIsLimit Seed pe A B includeProjection

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
