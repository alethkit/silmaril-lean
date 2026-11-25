module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Thms

/-! # Classes of exactly typed continuation families before normalization -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Continuation bodies can use arbitrary exactly typed branch arguments. -/
abbrev TypedContinuationFamily (Γ : VCtx τ) (L K : LCtx τ) :=
  {σ : Nat → Region Φ // LSubst.HasType Γ L K σ}

@[expose] def typedContinuationSetoid (Γ : VCtx τ) (L K : LCtx τ) :
    Setoid (TypedContinuationFamily (Φ := Φ) Γ L K) where
  r σ υ := ∀ ⦃ℓ A⦄, At L ℓ A → SubstitutionEquiv (A :: Γ) (σ.val ℓ) (υ.val ℓ) K
  iseqv := ⟨fun σ _ _ hℓ => .base (.refl (σ.property hℓ)),
    fun h _ _ hℓ => (h hℓ).symm, fun h h' _ _ hℓ => (h hℓ).trans (h' hℓ)⟩

/-- Pointwise native rewrite classes of all exactly typed families. -/
abbrev TypedContinuationClass (Γ : VCtx τ) (L K : LCtx τ) :=
  Quotient (typedContinuationSetoid (Φ := Φ) Γ L K)

variable {Γ : VCtx τ} {L K : LCtx τ}

/-- View a value-branch continuation as an exactly typed continuation. -/
@[expose] def ContinuationFamily.toTyped
    (σ : ContinuationFamily (Φ := Φ) Γ L K) : TypedContinuationFamily (Φ := Φ) Γ L K :=
  ⟨σ.val, fun _ _ hi => (σ.property hi).hasType⟩

/-- View an arrow of the continuation category as an exactly typed class. -/
@[expose] def ContinuationHom.toTypedClass (f : ContinuationHom (Φ := Φ) Γ L K) :
    TypedContinuationClass (Φ := Φ) Γ L K :=
  Quotient.map ContinuationFamily.toTyped (fun _ _ h => h) f

end Silmaril.Isotope.LambdaSSA.Region
