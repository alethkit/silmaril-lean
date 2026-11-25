module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Soundness
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.Defs

/-! # Evaluation of constructor-sequenced returns -/

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.RetainedLet (returnOnce)
open Paper.UnaryReturn.Beta.Constructors
open Silmaril.Isotope.LambdaSSA.Semantics (extend)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer (Env EnvTy Val Result)
open scoped Paper.BoundSimulation.Obstruction
open scoped Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer.CanonicalUnit

private theorem sequence_pair (a b : Tm Empty) (env : Env) :
    evalRegionWith false (returnOnce (.pair a b)) env =
      evalRegionWith false (pairSequence a b) env := by
  simp only [returnOnce, pairSequence, evalRegionWith, evalTermWith,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  cases evalTermWith false a env with
  | none => rfl
  | some v =>
    simp only [evalTerm_rename b (markPairLet := false) (env := env)
      (env' := extend env v) (ρ := Nat.succ) (fun _ => rfl)]
    cases evalTermWith false b env <;> rfl

private theorem sequence_inl (a : Tm Empty) (env : Env) :
    evalRegionWith false (returnOnce (.inl a)) env =
      evalRegionWith false (inlSequence a) env := by
  simp only [returnOnce, inlSequence, evalRegionWith, evalTermWith]
  cases evalTermWith false a env <;> rfl

private theorem sequence_inr (a : Tm Empty) (env : Env) :
    evalRegionWith false (returnOnce (.inr a)) env =
      evalRegionWith false (inrSequence a) env := by
  simp only [returnOnce, inrSequence, evalRegionWith, evalTermWith]
  cases evalTermWith false a env <;> rfl

/-- Opt-in constructor sequencing preserves the unmarked observation. -/
private theorem sequencing_same {Γ L : List (Ty Empty)} {r s : Region Empty}
    (h : Paper.WithConstructorSequencing.Eqv Γ r s L) : SameWith false Γ r s :=
  extension_same (markPairLet := false) (fun e =>
    Or.elim e unary_fusion_same (fun h => by
      cases h with
      | pair ha hb => exact fun env _ => sequence_pair _ _ env
      | inl ha => exact fun env _ => sequence_inl _ env
      | inr ha => exact fun env _ => sequence_inr _ env)) h

private def quote : Val → Tm Empty
  | .atom a => a.elim
  | .unit => .unit
  | .pair v w => .pair (quote v) (quote w)
  | .inl v => .inl (quote v)
  | .inr v => .inr (quote v)

private theorem eval_closed {Γ : VCtx (Ty Empty)} {t : Tm Empty} {A : Ty Empty}
    (ht : Tm.BranchValue Γ t A) (hΓ : Γ = []) (env : Env) :
    (evalTermWith false t env).map quote = some t := by
  induction ht with
  | var hi => subst Γ; cases hi
  | unit => rfl
  | pair _ _ ia ib =>
    obtain ⟨v, ev, hv⟩ := Option.map_eq_some_iff.mp ia
    obtain ⟨w, ew, hw⟩ := Option.map_eq_some_iff.mp ib
    simp [evalTermWith, ev, ew, quote, hv, hw]
  | inl _ ih =>
    obtain ⟨v, ev, hv⟩ := Option.map_eq_some_iff.mp ih
    simp [evalTermWith, ev, quote, hv]
  | inr _ ih =>
    obtain ⟨v, ev, hv⟩ := Option.map_eq_some_iff.mp ih
    simp [evalTermWith, ev, quote, hv]

theorem closed_branch_injective {t u : Tm Empty} {A : Ty Empty}
    (ht : Tm.BranchValue [] t A) (hu : Tm.BranchValue [] u A)
    (h : Paper.WithConstructorSequencing.Eqv [.unit] (.br 0 t) (.br 0 u) [A]) : t = u := by
  have env : EnvTy [.unit] (fun _ => .unit) := by
    intro i A hi
    cases i with
    | zero => cases Option.some.inj hi; exact .unit
    | succ i => cases i <;> contradiction
  have observed := sequencing_same h (fun _ => .unit) env
  obtain ⟨v, ev, hv⟩ := Option.map_eq_some_iff.mp (eval_closed ht rfl (fun _ => .unit))
  obtain ⟨w, ew, hw⟩ := Option.map_eq_some_iff.mp (eval_closed hu rfl (fun _ => .unit))
  simp only [evalRegionWith, ev, ew, Result.jump.injEq, true_and] at observed
  exact hv.symm.trans (observed ▸ hw)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer
