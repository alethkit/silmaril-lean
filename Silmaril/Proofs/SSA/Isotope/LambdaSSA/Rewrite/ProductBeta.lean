module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.ProductBeta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Thms

/-! # Constructor-pair typing and compatibility with unary β -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ProductBeta

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.ProductBeta

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

theorem step_typed {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (h : Step Γ r s L) :
    Region.HasType Γ r L ∧ Region.HasType Γ s L := by
  cases h with
  | let₂Beta ha hb hr =>
    exact ⟨.let₂ (.pair ha.hasType hb.hasType) hr,
      hr.substVars ((Tm.Subst.HasType.single ha.hasType).cons hb.hasType)⟩

theorem link_typed {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : Relation.SymmGen (fun r s => CfgEta.Eqv Γ r s L ∨ Step Γ r s L) r s) :
    Region.HasType Γ r L ∧ Region.HasType Γ s L := by
  rcases h with (h | h) | (h | h)
  · exact h.typed
  · exact step_typed h
  · exact ⟨h.typed.2, h.typed.1⟩
  · exact ⟨(step_typed h).2, (step_typed h).1⟩

theorem eqv_typed {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (h : Eqv Γ r s L) :
    Region.HasType Γ r L ∧ Region.HasType Γ s L := by
  induction h with
  | single h => exact link_typed h
  | tail _ h ih => exact ⟨ih.1, (link_typed h).2⟩

private theorem rename_succ_single (a b : Tm Φ) :
    (b.rename Nat.succ).subst (Tm.singleSubst a) = b := by
  rw [Tm.subst_rename]
  exact Tm.subst_var b

private theorem lift_single_pair (a b : Tm Φ) :
    (fun i => (Tm.liftSubst (Tm.singleSubst a) i).subst (Tm.singleSubst b)) =
      Tm.consSubst b (Tm.singleSubst a) := by
  funext i
  cases i with
  | zero => rfl
  | succ i => exact rename_succ_single b (Tm.singleSubst a i)

theorem let₂_pair {Γ : VCtx τ} {A B : τ} {L : LCtx τ}
    {a b : Tm Φ} {r : Region Φ} (ha : Tm.BranchValue Γ a A) (hb : Tm.BranchValue Γ b B)
    (hr : Region.HasType (B :: A :: Γ) r L) :
    Eqv Γ (.let₂ (.pair a b) r) (.let₁ a (.let₁ (b.rename Nat.succ) r)) L := by
  have h₁ := SubstitutionEquiv.letValue ha (.let₁ (hb.hasType.weaken A) hr)
  change SubstitutionEquiv Γ (.let₁ a (.let₁ (b.rename Nat.succ) r))
    (.let₁ ((b.rename Nat.succ).subst (Tm.singleSubst a))
      (r.substVars (Tm.liftSubst (Tm.singleSubst a)))) L at h₁
  rw [rename_succ_single] at h₁
  have h₂ := SubstitutionEquiv.letValue hb (hr.substVars ((Tm.Subst.HasType.single ha.hasType).lift B))
  have h := h₁.trans h₂
  rw [Region.substVars_comp, lift_single_pair] at h
  exact .tail (.single (.inl (.inr (Step.let₂Beta ha hb hr)))) (.inl (.inl (.native h.symm)))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ProductBeta
