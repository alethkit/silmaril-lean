module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.FlatDispatcher.Execution.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatExecutionRouting
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatExecutionFinite
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatDivergenceRouting

/-! # Coinductive divergence of the guarded packed flat CFG -/

public section

universe u v w x

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatExecution

open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.FiniteCFG
open Silmaril.Isotope.LambdaSSA.Region
open Semantics (extend Env Config)
open Semantics.External (Diverges)
open SyntacticCategory (iterationBody)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {blocks exits : Nat} {R : Fin blocks → τ} {E : Fin exits → τ}
  {g : FiniteCFG Φ blocks exits 0}
  {α : Type w} {σ : Type x} {instr : Φ → Value α → σ → Value α → σ → Prop}
  {prim : Φ → Value α → σ → Prop}

private theorem diverging_follow_inside {n i : Nat} {bs : Fin n → Region Φ}
    {env : Env α} {v : Value α} {s : σ}
    (h : Diverges instr prim (.follow env bs i v s)) : i < n := by
  cases h.unfold with
  | core h =>
    cases h with
    | follow_body inside _ | follow_next inside _ _ => exact inside

private theorem follow_diverges_pack (hg : FiniteCFG.HasType .nil R E g)
    {env : Env α} {i : Fin blocks} {v : Value α} {s : σ}
    (h : Diverges instr prim (.follow env (fun j => (g.block j).erase) i.val v s)) :
    Diverges instr prim (.follow env (fun _ : Fin 1 => iterationBody (packedDispatcherRegion hg))
      0 (packedExitValue i.val v) s) := by
  let invariant : Config α Φ σ → Prop := fun c => Diverges instr prim c ∨
    ∃ (j : Fin blocks) (value : Value α) (state : σ),
      c = .follow env (fun _ : Fin 1 => iterationBody (packedDispatcherRegion hg))
        0 (packedExitValue j.val value) state ∧
      Diverges instr prim (.follow env (fun k => (g.block k).erase) j.val value state)
  refine Diverges.coinduct invariant ?_ (.inr ⟨i, v, s, rfl, h⟩)
  rintro c (h | ⟨j, value, state, rfl, h⟩)
  · exact h.unfold.mono (fun _ h => .inl h)
  · apply Semantics.External.DivergenceStep.core
    cases h.unfold with
    | core h =>
      cases h with
      | follow_body _ h =>
        exact .follow_body (by decide) (.inl ((dispatcherBody_diverges_at hg j.isLt).mpr h))
      | follow_next _ run rest =>
        have inside := diverging_follow_inside rest
        have packed := (routedFlat_body_eval blocks (g.block j)).mpr ⟨_, _, run, rfl, rfl⟩
        simp only [feedbackLabel, feedbackPayload, ite_eq_left inside] at packed
        exact .follow_next (by decide) ((dispatcherBody_at hg j.isLt).mpr packed)
          (.inr ⟨⟨_, inside⟩, _, _, rfl, rest⟩)

private theorem follow_diverges_unpack (hg : FiniteCFG.HasType .nil R E g)
    {env : Env α} {i : Fin blocks} {v : Value α} {s : σ}
    (h : Diverges instr prim (.follow env (fun _ : Fin 1 => iterationBody (packedDispatcherRegion hg))
      0 (packedExitValue i.val v) s)) :
    Diverges instr prim (.follow env (fun j => (g.block j).erase) i.val v s) := by
  let invariant : Config α Φ σ → Prop := fun c => Diverges instr prim c ∨
    ∃ (j : Fin blocks) (value : Value α) (state : σ),
      c = .follow env (fun k => (g.block k).erase) j.val value state ∧
      Diverges instr prim (.follow env (fun _ : Fin 1 => iterationBody (packedDispatcherRegion hg))
        0 (packedExitValue j.val value) state)
  refine Diverges.coinduct invariant ?_ (.inr ⟨i, v, s, rfl, h⟩)
  rintro c (h | ⟨j, value, state, rfl, h⟩)
  · exact h.unfold.mono (fun _ h => .inl h)
  · apply Semantics.External.DivergenceStep.core
    cases h.unfold with
    | core h =>
      cases h with
      | follow_body _ h =>
        exact .follow_body j.isLt (.inl ((dispatcherBody_diverges_at hg j.isLt).mp h))
      | follow_next _ run rest =>
        obtain ⟨next, payload, run, label, tag⟩ :=
          (routedFlat_body_eval blocks (g.block j)).mp ((dispatcherBody_at hg j.isLt).mp run)
        have inside := diverging_follow_inside rest
        rw [label] at inside
        have nextInside : next < blocks := by
          by_contra! h
          simp [feedbackLabel, Nat.not_lt_of_ge h] at inside
        simp only [label, tag, feedbackLabel, feedbackPayload, ite_eq_left nextInside] at rest
        exact .follow_next j.isLt run (.inr ⟨⟨next, nextInside⟩, payload, _, rfl, rest⟩)

theorem packedExecution_external_diverges (hg : FiniteCFG.HasType .nil R E g)
    {env : Env α} {start : σ} :
    Diverges instr prim (.region env (packedExecutionRegion hg) start) ↔
      Diverges instr prim (.region env g.erase start) := by
  constructor
  · intro h
    cases h.unfold with
    | core h =>
      cases h with
      | cfg_entry rest =>
        exact .fold_core (.cfg_entry ((routedFlat_body_diverges blocks g.entry).mp rest))
      | cfg_follow entry rest =>
        obtain ⟨i, v, entry, label, tag⟩ := (routedFlat_body_eval blocks g.entry).mp entry
        have inside := diverging_follow_inside rest
        rw [label] at inside
        have originalInside : i < blocks := by
          by_contra! h
          simp [feedbackLabel, Nat.not_lt_of_ge h] at inside
        simp only [label, tag, feedbackLabel, feedbackPayload, ite_eq_left originalInside] at rest
        exact .fold_core (.cfg_follow entry (follow_diverges_unpack hg (i := ⟨i, originalInside⟩) rest))
  · intro h
    cases h.unfold with
    | core h =>
      cases h with
      | cfg_entry rest =>
        exact .fold_core (.cfg_entry ((routedFlat_body_diverges blocks g.entry).mpr rest))
      | cfg_follow entry rest =>
        have inside := diverging_follow_inside rest
        have packed := (routedFlat_body_eval blocks g.entry).mpr ⟨_, _, entry, rfl, rfl⟩
        simp only [feedbackLabel, feedbackPayload, ite_eq_left inside] at packed
        exact .fold_core (.cfg_follow packed (follow_diverges_pack hg (i := ⟨_, inside⟩) rest))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatExecution
