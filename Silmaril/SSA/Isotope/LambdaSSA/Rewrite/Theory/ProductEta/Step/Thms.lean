module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.ProductEta.Step.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Thms

/-! # Typed endpoints and renamings of variable product η -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.ProductEta

variable {τ : Type u} [TypeFormers τ] {Φ : Type v}
  {Γ Δ : VCtx τ} {L K : LCtx τ} {r s : Region Φ}

/-- A typed value renaming preserves the variable scrutinee. -/
theorem Step.renameVars (h : Step Γ r s L) {ρ : Nat → Nat} (hρ : Ren Γ Δ ρ) :
    Step Δ (r.renameVars ρ) (s.renameVars ρ) L := by
  cases h with
  | let₂Eta hi hℓ => exact .let₂Eta (hρ hi) hℓ

/-- A typed label renaming preserves the direct branch on each side. -/
theorem Step.renameLabels (h : Step Γ r s L) {ρ : Nat → Nat} (hρ : Ren L K ρ) :
    Step Γ (r.renameLabels ρ) (s.renameLabels ρ) K := by
  cases h with
  | let₂Eta hi hℓ => exact .let₂Eta hi (hρ hℓ)

/-- Forwarding exits by a typed label renaming is also a variable product η step. -/
theorem Step.lsubst_forward (h : Step Γ r s L) {ρ : Nat → Nat} (hρ : Ren L K ρ) :
    Step Γ (r.lsubst (labelId ∘ ρ)) (s.lsubst (labelId ∘ ρ)) K := by
  simpa only [renameLabels_eq_lsubst] using h.renameLabels hρ

variable [HasTy Φ τ]

/-- Both sides fit the constructor-valued branch presentation. -/
theorem Step.valueBranches (h : Step Γ r s L) : ValueBranches Γ r L ∧ ValueBranches Γ s L := by
  cases h with
  | let₂Eta hi hℓ => exact ⟨.let₂ (.var hi) (.br hℓ (.pair (.var rfl) (.var rfl))), .br hℓ (.var hi)⟩

/-- Both sides have the same exact typing interface. -/
theorem Step.typed (h : Step Γ r s L) : Region.HasType Γ r L ∧ Region.HasType Γ s L :=
  ⟨h.valueBranches.1.hasType, h.valueBranches.2.hasType⟩

end Silmaril.Isotope.LambdaSSA.Region.ProductEta
