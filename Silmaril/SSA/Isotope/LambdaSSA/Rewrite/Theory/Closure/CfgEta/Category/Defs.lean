module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Thms

/-! # Continuation classes for one-block literal CFG η -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- An exit interface for the opt-in CFG η presentation at a fixed capture context. -/
structure Interface (Φ : Type v) (Γ : VCtx τ) where
  labels : LCtx τ

@[expose] def familySetoid (Γ : VCtx τ) (L K : LCtx τ) :
    Setoid (ContinuationFamily (Φ := Φ) Γ L K) where
  r σ υ := Equivalent Γ L K σ.val υ.val
  iseqv := ⟨fun σ _ _ hi => .native (.base (.refl (σ.property hi).hasType)),
    fun h _ _ hi => (h hi).symm, fun h h' _ _ hi => (h hi).trans (h' hi)⟩

/-- Typed continuation families modulo pointwise one-block CFG η equivalence. -/
abbrev Hom (Γ : VCtx τ) (L K : LCtx τ) :=
  Quotient (familySetoid (Φ := Φ) Γ L K)

variable {Γ : VCtx τ} {L K P : LCtx τ}

@[expose] def Hom.identity (Γ : VCtx τ) (L : LCtx τ) : Hom (Φ := Φ) Γ L L :=
  Quotient.mk _ (ContinuationFamily.identity Γ L)

@[expose] def Hom.compose (f : Hom (Φ := Φ) Γ L K) (g : Hom (Φ := Φ) Γ K P) :
    Hom (Φ := Φ) Γ L P :=
  Quotient.map₂ ContinuationFamily.compose
    (fun σ _ hσ _ _ hυ => Equivalent.comp hσ hυ σ.property) f g

/-- Send a native continuation class to its class in the enlarged presentation. -/
@[expose] def Hom.ofNative (f : ContinuationHom (Φ := Φ) Γ L K) : Hom (Φ := Φ) Γ L K :=
  @Quotient.map _ _ (continuationSetoid Γ L K) (familySetoid Γ L K) id
    (fun σ υ h => by
      change (∀ ⦃i A⦄, At L i A → SubstitutionEquiv (A :: Γ) (σ.val i) (υ.val i) K) at h
      exact fun _ _ hi => Eqv.native (h hi)) f

end Silmaril.Isotope.LambdaSSA.Region.CfgEta
