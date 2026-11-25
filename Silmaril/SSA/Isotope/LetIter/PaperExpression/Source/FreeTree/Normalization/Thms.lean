module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Normalization.Result.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.SumSplit.FreeTree.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Normalization

/-! # Original-bound normalization and reflection for the pure source fragment -/

public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Normalization

universe u r

variable {α Φ : Type u} (S : Signature α Φ)
variable {ε : Type r} [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε]

variable {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α}

/-- Normalize a bottom-typed source expression in an atomic pure context.
The equation holds directly at the supplied original effect bound. -/
theorem normalize {a : Expr Φ} {A : Ty α}
    (h : letI := S.endpoints; Wf Γ a A (⊥ : ε))
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε) :
    letI := S.endpoints
    ∃ p : Value S slots A, p.Pure (ε := ε) S ∧ Eqv Γ A e a (p.source S) :=
  Proofs.normalize S h hΓ hslots e

/-- At an atomic result, normalization supplies a pure free tree. -/
theorem normalizesToTree {a : Expr Φ} {C : α}
    (h : letI := S.endpoints; Wf Γ a (.base C) (⊥ : ε))
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε) :
    SumSplit.NormalizesToTree S Γ slots e C a :=
  Proofs.normalizesToTree S h hΓ hslots e

variable [DecidableEq α] [EffectIteration ε]

/-- In a pure atomic input context, reflect native equality at any result type. -/
theorem endpoint_reflection_atomic_inputs {A : Ty α} {a b : Expr Φ}
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    (ha : letI := S.endpoints; Wf Γ a A (⊥ : ε))
    (hb : letI := S.endpoints; Wf Γ b A (⊥ : ε))
    {t s : Tm Empty Φ Γ.length}
    (ht : a.toLetIter Γ.length = some t) (hs : b.toLetIter Γ.length = some s) :
    letI := S.endpoints
    AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s A ↔ Eqv Γ A e a b :=
  Proofs.endpoint_reflection_atomic_inputs S hΓ hslots e ha hb ht hs

/-- Reflection for bottom-typed expressions in a pure atomic context. -/
theorem endpoint_reflection_atomic {a b : Expr Φ} {C : α}
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    (ha : letI := S.endpoints; Wf Γ a (.base C) (⊥ : ε))
    (hb : letI := S.endpoints; Wf Γ b (.base C) (⊥ : ε))
    {t s : Tm Empty Φ Γ.length}
    (ht : a.toLetIter Γ.length = some t) (hs : b.toLetIter Γ.length = some s) :
    letI := S.endpoints
    AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s (.base C) ↔
      Eqv Γ (.base C) e a b :=
  Proofs.endpoint_reflection_atomic S hΓ hslots e ha hb ht hs

/-- A single open sum with atomic payloads can be at any slot. The branch
witnesses are derived from bottom-effect source typing. -/
theorem endpoint_reflection_sum {a b : Expr Φ} {A B C : α}
    (i : Fin Γ.length) (hΓ : Γ.Pure)
    (hi : (Γ.get i).1 = .coprod (.base A) (.base B))
    (slotsL : Fin (SumSplit.branchCtx Γ i (.base A)).length → α)
    (slotsR : Fin (SumSplit.branchCtx Γ i (.base B)).length → α)
    (hslotsL : ∀ j, ((SumSplit.branchCtx Γ i (.base A)).get j).1 = .base (slotsL j))
    (hslotsR : ∀ j, ((SumSplit.branchCtx Γ i (.base B)).get j).1 = .base (slotsR j))
    (e : ε)
    (ha : letI := S.endpoints; Wf Γ a (.base C) (⊥ : ε))
    (hb : letI := S.endpoints; Wf Γ b (.base C) (⊥ : ε))
    {t s : Tm Empty Φ Γ.length}
    (ht : a.toLetIter Γ.length = some t) (hs : b.toLetIter Γ.length = some s) :
    letI := S.endpoints
    AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s (.base C) ↔
      Eqv Γ (.base C) e a b :=
  Proofs.endpoint_reflection_sum S i hΓ hi slotsL slotsR hslotsL hslotsR e ha hb ht hs

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Normalization
