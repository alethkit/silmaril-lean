module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.Packing

/-! # Maps of fixed-effect source quotients -/

public section

universe u v w

namespace Silmaril.Isotope.LetIter.PaperExpression.Source

variable {τ : Type u} {Φ : Type v} {ε : Type w}
  [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Preorder ε] [OrderBot ε]
  {Γ : EffectCtx τ ε} {A : τ} {e hi : ε}

theorem packExpr_wf {a : Expr Φ} (h : Wf Γ a A e) : Wf [(packType Γ, ⊥)] (packExpr a) A e :=
  Proofs.pack_wf h

theorem packExpr_eqv {a b : Expr Φ} (h : Eqv Γ A e a b) :
    Eqv [(packType Γ, ⊥)] A e (packExpr a) (packExpr b) :=
  Proofs.pack_eqv h

theorem unpackExpr_wf {a : Expr Φ} (hp : Γ.Pure) (h : Wf [(packType Γ, ⊥)] a A e) :
    Wf Γ (unpackExpr Γ a) A e :=
  Proofs.unpack_wf hp h

theorem unpackExpr_eqv {a b : Expr Φ} (hp : Γ.Pure) (h : Eqv [(packType Γ, ⊥)] A e a b) :
    Eqv Γ A e (unpackExpr Γ a) (unpackExpr Γ b) :=
  Proofs.unpack_eqv hp h

theorem denoteExpr_wf {a : Expr Φ} (h : Wf Γ a A e) :
    Wf [(packType Γ, ⊥)] (denoteExpr a) A e :=
  (Proofs.eqv_typed (Proofs.denote_eqv_pack h)).1

theorem wf_weakenEffect {a : Expr Φ} (d : Wf Γ a A e) (h : e ≤ hi) : Wf Γ a A hi :=
  Proofs.wf_wkEff d h

theorem eqv_weakenEffect {a b : Expr Φ} (d : Eqv Γ A e a b) (h : e ≤ hi) : Eqv Γ A hi a b :=
  Proofs.eqv_wkEff d h

/-- The source class of a typed expression. -/
@[expose] def ofExpr (a : TypedExpr Φ Γ A e) : Class Φ Γ A e := Quotient.mk _ a

/-- Replacing context variables by projections descends to source classes at the original bound. -/
@[expose] def pack : Class Φ Γ A e → Hom Φ (packType Γ) A e :=
  Quotient.map (fun a => ⟨packExpr a.val, packExpr_wf a.prop⟩)
    (fun _ _ h => packExpr_eqv h)

/-- The tuple of original variables reopens a packed expression in a pure context. -/
@[expose] def unpack (hp : Γ.Pure) : Hom Φ (packType Γ) A e → Class Φ Γ A e :=
  Quotient.map (fun a => ⟨unpackExpr Γ a.val, unpackExpr_wf hp a.prop⟩)
    (fun _ _ h => unpackExpr_eqv hp h)

/-- The source expression interpretation obtained by evaluating constructors
on the singleton environment. -/
@[expose] def denote (a : TypedExpr Φ Γ A e) : Hom Φ (packType Γ) A e :=
  ofExpr ⟨denoteExpr a.val, denoteExpr_wf a.prop⟩

/-- Change the upper bound of a source class. The underlying expression is preserved. -/
@[expose] def weakenEffect (h : e ≤ hi) : Class Φ Γ A e → Class Φ Γ A hi :=
  Quotient.map (fun a => ⟨a.val, wf_weakenEffect a.prop h⟩)
    (fun _ _ related => eqv_weakenEffect related h)

end Silmaril.Isotope.LetIter.PaperExpression.Source
