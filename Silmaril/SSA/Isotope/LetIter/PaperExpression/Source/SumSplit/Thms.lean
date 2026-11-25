module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.SumSplit.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.SumSplit

/-! # Typed sum specialization and reconstruction at the original effect bound -/

public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.SumSplit

universe u v w

variable {τ : Type u} {Φ : Type v} {ε : Type w}

variable [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Preorder ε] [OrderBot ε]
variable {Γ : EffectCtx τ ε} {A B C X : τ} {e : ε} {a b : Expr Φ}

omit [TypeFormers τ] in
/-- Replacing one slot by a bottom-annotated payload preserves purity of the context. -/
theorem branchCtx_pure (hΓ : Γ.Pure) (i : Fin Γ.length) (X : τ) :
    (branchCtx Γ i X).Pure :=
  Proofs.branchCtx_pure hΓ i X

/-- Each injection specialization keeps the same result type and effect bound. -/
theorem wf_specializations (i : Fin Γ.length) (ht : (Γ.get i).1 = coprod A B)
    (he : (Γ.get i).2 = ⊥) (ha : Wf Γ a C e) :
    Wf (branchCtx Γ i A) (left i a) C e ∧ Wf (branchCtx Γ i B) (right i a) C e :=
  Proofs.wf_specializations i ht he ha

/-- Rebuild an expression by casing on a pure sum slot and weakening its specializations. -/
theorem eqv_rebuild (i : Fin Γ.length) (ht : (Γ.get i).1 = coprod A B)
    (he : (Γ.get i).2 = ⊥) (ha : Wf Γ a C e) :
    Eqv Γ C e a (rebuild i a) :=
  Proofs.eqv_rebuild i ht he ha

/-- The two injection specializations characterize source equality at the same bound. -/
theorem eqv_iff_specializations (i : Fin Γ.length) (ht : (Γ.get i).1 = coprod A B)
    (he : (Γ.get i).2 = ⊥) (ha : Wf Γ a C e) (hb : Wf Γ b C e) :
    Eqv Γ C e a b ↔
      Eqv (branchCtx Γ i A) C e (left i a) (left i b) ∧
      Eqv (branchCtx Γ i B) C e (right i a) (right i b) :=
  Proofs.eqv_iff_specializations i ht he ha hb

end Silmaril.Isotope.LetIter.PaperExpression.Source.SumSplit
