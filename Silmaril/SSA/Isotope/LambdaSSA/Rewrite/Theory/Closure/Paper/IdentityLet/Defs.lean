module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Let.Identity.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Defs

/-! # An optional guarded identity-let equation -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.IdentityLet

open CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Contract identity lets inside an arbitrary exactly typed expression
evaluated by a region let. The fixed continuation uses constructor-valued
branch arguments. -/
inductive Step : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop where
  | let₁ {Γ : VCtx τ} {A : τ} {L : LCtx τ} {s t : Tm Φ} {r : Region Φ}
      {hs : Tm.HasType Γ s A} {ht : Tm.HasType Γ t A}
      (h : Tm.IdentityLet hs ht) (hr : ValueBranches (A :: Γ) r L) :
      Step Γ (.let₁ s r) (.let₁ t r) L

abbrev Eqv := Extension.Eqv (Step (τ := τ) (Φ := Φ))

abbrev projection : Paper.TypeCategory (τ := τ) Φ ⥤ Extension.Singleton.TypeCategory (Step (τ := τ) (Φ := Φ)) :=
  Extension.Singleton.projection Step

theorem Step.valueBranches {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : Step Γ r s L) : ValueBranches Γ r L ∧ ValueBranches Γ s L := by
  cases h with
  | @let₁ A L s t r hs ht _ hr => exact ⟨.let₁ hs hr, .let₁ ht hr⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.IdentityLet
