module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Iteration.Defs

/-! # One-block literal CFG η

This presentation extends the native rules with one-block CFG η for
literal label substitution. Categorical soundness is stated for shared
tensor comparisons in the corresponding soundness header.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta

open Silmaril.DeBruijn (lift)
open SyntacticCategory (iterateRegion)

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Form a CFG with one local label. -/
def singleCfg (entry block : Region Φ) : Region Φ :=
  .cfg entry 1 (fun _ => block)

/-- Enter the same one-block CFG at a selected payload. -/
def reentry (block : Region Φ) : Nat → Region Φ :=
  cfgEntryContinuations (fun _ : Fin 1 => block)

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The separate one-block literal CFG η presentation. Its new equation
scheme `etaPost` admits any typed outgoing substitution. Its CFG entry
and block have constructor-valued branch arguments. -/
inductive Eqv : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop where
  | native : SubstitutionEquiv Γ r s L → Eqv Γ r s L
  | symm : Eqv Γ r s L → Eqv Γ s r L
  | trans : Eqv Γ r s L → Eqv Γ s t L → Eqv Γ r t L
  | let₁ (ha : Tm.HasType Γ a A) (hr : Eqv (A :: Γ) r s L) :
      Eqv Γ (.let₁ a r) (.let₁ a s) L
  | let₂ (ha : Tm.HasType Γ a (Silmaril.product A B)) (hr : Eqv (B :: A :: Γ) r s L) :
      Eqv Γ (.let₂ a r) (.let₂ a s) L
  | case (ha : Tm.HasType Γ a (Silmaril.coprod A B))
      (hl : Eqv (A :: Γ) l l' L) (hr : Eqv (B :: Γ) r r' L) :
      Eqv Γ (.case a l r) (.case a l' r') L
  | cfg (R : Fin n → τ) (he : Eqv Γ entry entry' (List.ofFn R ++ L))
      (hb : ∀ i, Eqv (R i :: Γ) (bs i) (bs' i) (List.ofFn R ++ L)) :
      Eqv Γ (.cfg entry n bs) (.cfg entry' n bs') L
  | etaPost (he : ValueBranches Γ entry (A :: L))
      (hb : ValueBranches (A :: Γ) block (A :: L))
      (hσ : LSubst.HasType Γ L K σ) :
      Eqv Γ ((singleCfg entry block).lsubst σ) ((entry.lsubst (reentry block)).lsubst σ) K

/-- Pointwise equivalence at each exactly typed continuation label. -/
def Equivalent (Γ : VCtx τ) (L K : LCtx τ) (σ υ : Nat → Region Φ) : Prop :=
  ∀ ⦃i A⦄, At L i A → Eqv (A :: Γ) (σ i) (υ i) K

/-- Decode the sum exit into a return or another iteration. The repeat
arm drops the original state and the decoded sum slot. -/
def returnOrRepeat (A : τ) (p : Region Φ) : Region Φ :=
  .case (.var 0) (.br 0 (.var 0))
    ((iterateRegion A p).renameVars (lift (Nat.succ ∘ Nat.succ)))

end Silmaril.Isotope.LambdaSSA.Region.CfgEta
