module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.SumSplit.FreeTree.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.SumSplit.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.SumSplit.FreeTree

/-! # Original-bound reflection with explicit free-tree branch normal forms -/

public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.SumSplit

universe u r
variable {α Φ : Type u} (S : FreeTree.Signature α Φ)
  {ε : Type r} [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
variable {Γ : EffectCtx (Ty α) ε} {e : ε} {A B C : α}
  {a b : Expr Φ} {t s : Tm Empty Φ Γ.length}

/-- Two supplied free-tree normal forms suffice to reflect a native equality
in a pure atomic context. -/
theorem eqv_of_native_of_tree_normal_forms
    {sorts : Fin Γ.length → α} [DecidableEq α] (hΓ : Γ.Pure)
    (hslots : ∀ i, (Γ.get i).1 = .base (sorts i))
    (ht : a.toLetIter Γ.length = some t) (hs : b.toLetIter Γ.length = some s)
    (hn : letI := S.endpoints
      AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s (.base C))
    (h₁ : NormalizesToTree S Γ sorts e C a) (h₂ : NormalizesToTree S Γ sorts e C b) :
    letI := S.endpoints
    Eqv Γ (.base C) e a b :=
  TreeProofs.eqv_of_native_of_tree_normal_forms S hΓ hslots ht hs hn h₁ h₂

/-- Reflect arbitrary native equality of the open endpoints, given a pure
free-tree normal form for each of their two source specializations. -/
theorem endpoint_reflection [DecidableEq α]
    (i : Fin Γ.length) (hΓ : Γ.Pure)
    (hi : (Γ.get i).1 = .coprod (.base A) (.base B))
    (slotsL : Fin (branchCtx Γ i (.base A)).length → α)
    (slotsR : Fin (branchCtx Γ i (.base B)).length → α)
    (hslotsL : ∀ j, ((branchCtx Γ i (.base A)).get j).1 = .base (slotsL j))
    (hslotsR : ∀ j, ((branchCtx Γ i (.base B)).get j).1 = .base (slotsR j))
    (ha : letI := S.endpoints; Wf Γ a (.base C) e)
    (hb : letI := S.endpoints; Wf Γ b (.base C) e)
    (ht : a.toLetIter Γ.length = some t) (hs : b.toLetIter Γ.length = some s)
    (hLa : NormalizesToTree S (branchCtx Γ i (.base A)) slotsL e C (left i a))
    (hLb : NormalizesToTree S (branchCtx Γ i (.base A)) slotsL e C (left i b))
    (hRa : NormalizesToTree S (branchCtx Γ i (.base B)) slotsR e C (right i a))
    (hRb : NormalizesToTree S (branchCtx Γ i (.base B)) slotsR e C (right i b)) :
    letI := S.endpoints
    AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s (.base C) ↔
      Eqv Γ (.base C) e a b :=
  TreeProofs.endpoint_reflection S i hΓ hi slotsL slotsR hslotsL hslotsR
    ha hb ht hs hLa hLb hRa hRb

end Silmaril.Isotope.LetIter.PaperExpression.Source.SumSplit
