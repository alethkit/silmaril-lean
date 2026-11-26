module

public import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Descent.Literal
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Closure
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Descent

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.DeBruijn (lift)
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.Region (ValueBranches cfgEntryContinuations)
open Silmaril.Isotope.LambdaSSA.Region.CfgEta (singleCfg reentry)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Feedback
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation (Ops RegionAt)

universe u v w x

variable {Φ : Type u} {α : Type w} {σ : Type x} {O : Ops Φ α σ} {env : Env α}

private theorem resume_capture {n : Nat} (bs : Fin n → Region Φ) (a : Value α) (p : Jump α σ) (o : Exit α σ) :
    resume O (extend env a) (fun i => (bs i).renameVars (lift Nat.succ)) p o ↔ resume O env bs p o := by
  let f := followGraph O.instr O.faults O.prim (extend env a) (fun i => (bs i).renameVars (lift Nat.succ))
  let g := followGraph O.instr O.faults O.prim env bs
  have same (i : Fin n) (v : Value α) :
      RegionAt O (extend (extend env a) v) ((bs i).renameVars (lift Nat.succ)) (extend env v) (bs i) :=
    vars (bs i) (ρ := lift Nat.succ) (fun j => by cases j <;> rfl)
  have steps : f.step = g.step := by
    funext p q
    apply propext
    unfold f g followGraph
    exact exists_congr fun h => and_congr_right fun _ => (same ⟨p.label, h⟩ p.payload).eval
  have finish : f.finish = g.finish := by
    funext p o
    apply propext
    cases o with
    | ret =>
      apply or_congr_right
      exact exists_congr fun h => (same ⟨p.label, h⟩ p.payload).eval
    | fault =>
      exact exists_congr fun h => (same ⟨p.label, h⟩ p.payload).fault
    | diverge =>
      exact exists_congr fun h => (same ⟨p.label, h⟩ p.payload).div
  change o ∈ f.outcomes p ↔ o ∈ g.outcomes p
  simp only [Graph.outcomes, Graph.Finite, Graph.Reaches, Graph.Infinite, steps, finish]
  rfl

private theorem reentry_runs {n : Nat} (bs : Fin n → Region Φ) (p : Jump α σ) (o : Exit α σ) :
    continuation O env (cfgEntryContinuations bs) p o ↔ resume O env bs p o := by
  change Runs O (extend env p.payload)
    (.cfg (.br p.label (.var 0)) n (fun i => (bs i).renameVars (lift Nat.succ))) p.state o ↔ _
  rw [cfg_runs]
  have entry (d : Exit α σ) :
      Runs O (extend env p.payload) (.br p.label (.var 0)) p.state d ↔
        d = .ret p.label p.payload p.state := by
    constructor
    · intro run
      cases d with
      | ret => cases run with | br arg => cases arg; rfl
      | fault => cases run with | br arg => cases arg
      | diverge =>
        cases (show External.Diverges O.instr O.prim _ from run).unfold with
        | br arg => cases arg
        | core step => cases step
    · rintro rfl
      exact Semantics.Region.Eval.br .var
  simp only [entry, exists_eq_left]
  exact resume_capture bs p.payload p o

private theorem eta_unpost {τ : Type v} [TypeFormers τ] [HasTy Φ τ] {Γ L : List τ} {A : τ}
    {e b : Region Φ} (he : ValueBranches Γ e (A :: L)) :
    RegionAt O env (singleCfg e b) env (e.lsubst (reentry b)) := by
  apply regionAt_iff.mpr
  intro s o
  rw [show singleCfg e b = .cfg e 1 (fun _ => b) from rfl, cfg_runs,
    (literal (O := O) (env := env) he (reentry b)) s o]
  apply exists_congr
  intro d
  apply and_congr_right
  intro _
  cases d
  · exact (reentry_runs (fun _ : Fin 1 => b) _ _).symm
  · rfl
  · rfl

/-- The postcontinuation is arbitrary. Both producer spellings are guarded,
so both start it only after the same successful transfer at the same state. -/
theorem etaPost {τ : Type v} [TypeFormers τ] [HasTy Φ τ] {Γ L : List τ} {A : τ} {e b : Region Φ}
    (he : ValueBranches Γ e (A :: L)) (hb : ValueBranches (A :: Γ) b (A :: L)) (k : Nat → Region Φ) :
    RegionAt O env ((singleCfg e b).lsubst k) env ((e.lsubst (reentry b)).lsubst k) := by
  have left : ValueBranches Γ (singleCfg e b) L :=
    .cfg (fun _ : Fin 1 => A) he (fun _ => hb)
  have right := he.lsubst (Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.reentry_values hb)
  apply regionAt_iff.mpr
  intro s o
  rw [literal left k s o, literal right k s o]
  exact exists_congr fun d => and_congr_left' (regionAt_iff.mp (eta_unpost he) s d)

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Descent
