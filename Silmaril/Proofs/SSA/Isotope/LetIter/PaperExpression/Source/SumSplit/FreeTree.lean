module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.SumSplit.FreeTree.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.SumSplit.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.SumSplit
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Substitution.Thms

/-! # Reflection after splitting one source sum slot -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source


namespace Silmaril.Isotope.LetIter.PaperExpression.Source.SumSplit.TreeProofs

universe u v w

section Native

variable {τ : Type u} {Φ : Type v} {ε : Type w}
  [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]

/-- A typed source substitution from a bottom-annotated context lowers to a
pure native substitution. The existing native preservation theorem applies to
the entire derivation of the original equality. -/
theorem native_subst {Γ Δ : EffectCtx τ ε} (hΓ : Γ.Pure)
    {a b : Expr Φ} {σ : Nat → Expr Φ} {C : τ}
    {t s : Tm Empty Φ Γ.length}
    (ht : a.toLetIter Γ.length = some t) (hs : b.toLetIter Γ.length = some s)
    (hn : AbortEquiv (⊥ : ε) (.nil : Ctx Empty τ) Γ.toBoundCtx t s C)
    (hσ : Source.Proofs.TypedSubst Δ Γ σ) :
    ∃ t' s' : Tm Empty Φ Δ.length,
      (a.subst σ).toLetIter Δ.length = some t' ∧
      (b.subst σ).toLetIter Δ.length = some s' ∧
      AbortEquiv (⊥ : ε) (.nil : Ctx Empty τ) Δ.toBoundCtx t' s' C := by
  classical
  have hw (i : Fin Γ.length) : Wf Δ (σ i.val) (Γ.get i).1 (⊥ : ε) := hΓ i ▸ hσ i
  choose θ hθ htyped using fun i => (hw i).toLetIter
  have sub : PureTypedSubst (⊥ : ε) (.nil : Ctx Empty τ) Γ.toBoundCtx Δ.toBoundCtx θ :=
    ⟨fun i => (EffectCtx.get_toBoundCtx Γ i).symm ▸ (htyped i).1,
      fun i => (hw i).pure_toLetIter (hθ i)⟩
  exact ⟨_, _, Expr.toLetIter_subst ht hθ, Expr.toLetIter_subst hs hθ, hn.bsubst sub⟩

end Native

section Trees

universe r
variable {α Φ : Type u} (S : FreeTree.Signature α Φ)
  {ε : Type r} [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
variable {Γ : EffectCtx (Ty α) ε} {e : ε} {A B C : α}
  {a b : Expr Φ} {t s : Tm Empty Φ Γ.length}

theorem eqv_of_native_of_tree_normal_forms
    {sorts : Fin Γ.length → α} [DecidableEq α] (hΓ : Γ.Pure)
    (hslots : ∀ i, (Γ.get i).1 = .base (sorts i))
    (ht : a.toLetIter Γ.length = some t) (hs : b.toLetIter Γ.length = some s)
    (hn : letI := S.endpoints
      AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s (.base C))
    (h₁ : NormalizesToTree S Γ sorts e C a) (h₂ : NormalizesToTree S Γ sorts e C b) :
    letI := S.endpoints
    Eqv Γ (.base C) e a b := by
  let instr := S.endpoints
  obtain ⟨tN, htPure, hta⟩ := h₁
  obtain ⟨sN, hsPure, hsb⟩ := h₂
  have htn' : tN.source.toLetIter Γ.length = some tN.native := FreeTree.tree_lowers S tN
  have hsn' : sN.source.toLetIter Γ.length = some sN.native := FreeTree.tree_lowers S sN
  have htEq := hta.toLetIter ht htn'
  have hsEq := hsb.toLetIter hs hsn'
  have hNative := Refinement.trans htEq.symm (Refinement.trans hn hsEq)
  have hTrees := (FreeTree.endpoint_conservativity S tN sN htPure hsPure hΓ hslots e).mp hNative
  exact hta.trans (hTrees.trans hsb.symm)

public theorem endpoint_reflection [DecidableEq α]
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
      Eqv Γ (.base C) e a b := by
  let instr := S.endpoints
  constructor
  · intro h
    obtain ⟨_, _, lt, ls, lh⟩ := native_subst hΓ ht hs h (Proofs.left_typed i hi (hΓ i))
    obtain ⟨_, _, rt, rs, rh⟩ := native_subst hΓ ht hs h (Proofs.right_typed i hi (hΓ i))
    have hL := eqv_of_native_of_tree_normal_forms S (branchCtx_pure hΓ i _) hslotsL lt ls lh hLa hLb
    have hR := eqv_of_native_of_tree_normal_forms S (branchCtx_pure hΓ i _) hslotsR rt rs rh hRa hRb
    exact (eqv_iff_specializations i hi (hΓ i) ha hb).mpr ⟨hL, hR⟩
  · intro h
    exact h.toLetIter ht hs

end Trees

end Silmaril.Isotope.LetIter.PaperExpression.Source.SumSplit.TreeProofs
