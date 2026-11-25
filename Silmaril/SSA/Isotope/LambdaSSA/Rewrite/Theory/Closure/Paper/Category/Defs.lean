module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Transport.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Defs

/-! # Continuation classes in the paper relation -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Exit interfaces with a fixed capture context and instruction signature. -/
structure Interface (Φ : Type v) (Γ : VCtx τ) where
  labels : LCtx τ

@[expose] def familySetoid (Γ : VCtx τ) (L K : LCtx τ) :
    Setoid (ContinuationFamily (Φ := Φ) Γ L K) where
  r σ υ := ∀ ⦃i A⦄, At L i A → Eqv (A :: Γ) (σ.val i) (υ.val i) K
  iseqv := ⟨fun σ _ _ hi => .cfgEta (.native (.base (.refl (σ.property hi).hasType))),
    fun h _ _ hi => (h hi).symm, fun h h' _ _ hi => (h hi).trans (h' hi)⟩

/-- Pointwise paper classes of exactly typed continuation families with
constructor-valued branch arguments. -/
abbrev Hom (Γ : VCtx τ) (L K : LCtx τ) :=
  Quotient (familySetoid (Φ := Φ) Γ L K)

variable {Γ : VCtx τ} {L K P : LCtx τ}

@[expose] def Hom.identity (Γ : VCtx τ) (L : LCtx τ) : Hom (Φ := Φ) Γ L L :=
  Quotient.mk _ (ContinuationFamily.identity Γ L)

@[expose] def Hom.compose (f : Hom (Φ := Φ) Γ L K) (g : Hom (Φ := Φ) Γ K P) :
    Hom (Φ := Φ) Γ L P :=
  Quotient.map₂ ContinuationFamily.compose
    (fun σ σ' hσ _ _ hυ => compLSubst_congr hσ hυ σ.property σ'.property) f g

/-- Include CFG η equations in the larger relation while keeping each
representative and its value-branch witness. -/
@[expose] def Hom.ofCfgEta (f : CfgEta.Hom (Φ := Φ) Γ L K) : Hom (Φ := Φ) Γ L K :=
  Quotient.map id (fun (σ υ : ContinuationFamily Γ L K) h => by
    change CfgEta.Equivalent Γ L K σ.val υ.val at h
    exact fun _ _ hi => Eqv.cfgEta (h hi)) f

end Silmaril.Isotope.LambdaSSA.Region.Paper
