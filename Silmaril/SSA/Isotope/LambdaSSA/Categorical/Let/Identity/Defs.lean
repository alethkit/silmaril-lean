module

public import Silmaril.SSA.Isotope.LambdaSSA.Typing.Defs

/-! # Identity lets in exactly typed expression contexts -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Tm

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Remove an identity let at any typed expression position. The indices
record both endpoints at the same context and result type, including
positions below binders. -/
inductive IdentityLet :
    {Γ : VCtx τ} → {s t : Tm Φ} → {A : τ} → HasType Γ s A → HasType Γ t A → Prop where
  | same {Γ : VCtx τ} {t : Tm Φ} {A : τ} (ht : HasType Γ t A) : IdentityLet ht ht
  | remove {Γ : VCtx τ} {t : Tm Φ} {A : τ} (ht : HasType Γ t A) :
      IdentityLet (.let₁ ht (.var (i := 0) rfl)) ht
  | op {Γ : VCtx τ} {f : Φ} {s t : Tm Φ}
      {hs : HasType Γ s (instrSrc f)} {ht : HasType Γ t (instrSrc f)}
      (h : IdentityLet hs ht) : IdentityLet (.op (f := f) hs) (.op (f := f) ht)
  | let₁ {Γ : VCtx τ} {A B : τ} {a a' b b' : Tm Φ}
      {ha : HasType Γ a A} {ha' : HasType Γ a' A}
      {hb : HasType (A :: Γ) b B} {hb' : HasType (A :: Γ) b' B}
      (h : IdentityLet ha ha') (k : IdentityLet hb hb') :
      IdentityLet (.let₁ ha hb) (.let₁ ha' hb')
  | pair {Γ : VCtx τ} {A B : τ} {a a' b b' : Tm Φ}
      {ha : HasType Γ a A} {ha' : HasType Γ a' A} {hb : HasType Γ b B} {hb' : HasType Γ b' B}
      (h : IdentityLet ha ha') (k : IdentityLet hb hb') :
      IdentityLet (.pair ha hb) (.pair ha' hb')
  | let₂ {Γ : VCtx τ} {A B D : τ} {a a' b b' : Tm Φ}
      {ha : HasType Γ a (Silmaril.product A B)} {ha' : HasType Γ a' (Silmaril.product A B)}
      {hb : HasType (B :: A :: Γ) b D} {hb' : HasType (B :: A :: Γ) b' D}
      (h : IdentityLet ha ha') (k : IdentityLet hb hb') :
      IdentityLet (.let₂ ha hb) (.let₂ ha' hb')
  | inl {Γ : VCtx τ} {A B : τ} {s t : Tm Φ} {hs : HasType Γ s A} {ht : HasType Γ t A}
      (h : IdentityLet hs ht) : IdentityLet (.inl (B := B) hs) (.inl (B := B) ht)
  | inr {Γ : VCtx τ} {A B : τ} {s t : Tm Φ} {hs : HasType Γ s B} {ht : HasType Γ t B}
      (h : IdentityLet hs ht) : IdentityLet (.inr (A := A) hs) (.inr (A := A) ht)
  | case {Γ : VCtx τ} {A B D : τ} {e e' l l' r r' : Tm Φ}
      {he : HasType Γ e (Silmaril.coprod A B)} {he' : HasType Γ e' (Silmaril.coprod A B)}
      {hl : HasType (A :: Γ) l D} {hl' : HasType (A :: Γ) l' D}
      {hr : HasType (B :: Γ) r D} {hr' : HasType (B :: Γ) r' D}
      (h : IdentityLet he he') (left : IdentityLet hl hl') (right : IdentityLet hr hr') :
      IdentityLet (.case he hl hr) (.case he' hl' hr')
  | abort {Γ : VCtx τ} {A : τ} {s t : Tm Φ}
      {hs : HasType Γ s Silmaril.empty} {ht : HasType Γ t Silmaril.empty}
      (h : IdentityLet hs ht) : IdentityLet (.abort (A := A) hs) (.abort (A := A) ht)

end Silmaril.Isotope.LambdaSSA.Tm
