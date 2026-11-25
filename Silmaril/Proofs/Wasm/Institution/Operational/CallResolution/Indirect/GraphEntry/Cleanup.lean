module

public import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Core
public import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Lime1
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Proofs

open Execution
open Execution.Runtime (Frame Value)
open CallContinuation
open CallContinuation.OuterCall
open CallContinuation.OuterCall.Computed
open Wasm.SingleThreaded.Det (noHost)

private theorem core_cleanup_step {H : Type} {P : Numerics.Profile} {s : Core.Store H}
    {entry : Entry} {outer inner : Frame} (a : Cleanup Core.Admin) (dst : Core.Config H) :
    Core.Step P noHost (entry.coreCleanup s outer inner a) dst ↔
      ∃ out, CleanupStep a out ∧ dst = entry.coreCleanup s outer inner out := by
  cases a with
  | label stack rest =>
    constructor
    · intro move
      rcases Computed.core_body_step_cases move with ⟨mid, inside, eq⟩ | ⟨out, pop, eq⟩
      · have moved := (Prefix.core_discard_iff (P := P) (s := s) (f := inner) id (stack := stack)
          (tail := rest) (dst := mid)).mp (by simpa only [List.map_id] using inside)
        obtain ⟨kept, remaining, cut, midEq⟩ := moved
        exact ⟨.label kept remaining, .discard cut, by simpa only [Entry.coreCleanup,
          Context.Resume.Continuation.coreWrap, midEq, List.map_id] using eq⟩
      · have stopped : stack = [] ∧ rest = [] := by
          by_contra notEmpty
          exact Computed.core_label_stays (head := .trap) rfl (by simp) (by simp)
            (by simp [Core.Admin.IsReturnCallRef]) (by simp)
            (fun _ => by
              rcases not_and_or.mp notEmpty with stackNonempty | restNonempty
              · exact .inl (fun nil => stackNonempty (List.map_eq_nil_iff.mp nil))
              · exact .inr restNonempty) pop
        obtain ⟨rfl, rfl⟩ := stopped
        exact ⟨.frame, .label, eq.trans (by rw [Nested.core_label_result (r := .trap) pop]; rfl)⟩
    · rintro ⟨out, step, rfl⟩
      cases step with
      | discard cut =>
        apply Core.Step.ctxtFrame
        apply Core.Step.ctxtLabel
        simpa only [List.map_id] using (Prefix.core_discard_iff (P := P) (s := s) (f := inner) id).mpr
          ⟨_, _, cut, by simp only [List.map_id]⟩
      | label => exact Core.Step.ctxtFrame .trapLabel
  | frame =>
    constructor
    · intro move
      exact ⟨.done, .frame, Nested.core_frame_result (r := .trap) move⟩
    · rintro ⟨out, step, rfl⟩
      cases step
      exact .trapFrame
  | done =>
    exact iff_of_false (fun h => Nested.core_result_stuck (r := .trap) h) (by
      rintro ⟨out, step, _⟩
      cases step)

open Wasm.Lime1.Execution in
private theorem lime_cleanup_step {H : Type} {s : Store H} {entry : Entry} {outer inner : Frame}
    (a : Cleanup Admin) (dst : Config H) :
    Step CallFrame.limeNoHost (entry.limeCleanup s outer inner a) dst ↔
      ∃ out, CleanupStep a out ∧ dst = entry.limeCleanup s outer inner out := by
  cases a with
  | label stack rest =>
    constructor
    · intro move
      rcases Computed.lime_body_step_cases move with ⟨mid, inside, eq⟩ | ⟨out, pop, eq⟩
      · have moved := (Prefix.lime_discard_iff (s := s) (f := inner) id (stack := stack)
          (tail := rest) (dst := mid)).mp (by simpa only [List.map_id] using inside)
        obtain ⟨kept, remaining, cut, midEq⟩ := moved
        exact ⟨.label kept remaining, .discard cut, by simpa only [Entry.limeCleanup,
          Context.Resume.Continuation.limeWrap, midEq, List.map_id] using eq⟩
      · have stopped : stack = [] ∧ rest = [] := by
          by_contra notEmpty
          exact Computed.lime_label_stays (head := .trap) rfl (by simp) (by simp)
            (fun _ => not_and_or.mp notEmpty) pop
        obtain ⟨rfl, rfl⟩ := stopped
        exact ⟨.frame, .label, eq.trans (by rw [Nested.lime_label_result (r := .trap) pop]; rfl)⟩
    · rintro ⟨out, step, rfl⟩
      cases step with
      | discard cut =>
        apply Step.frame
        apply Step.label
        simpa only [List.map_id] using (Prefix.lime_discard_iff (s := s) (f := inner) id).mpr
          ⟨_, _, cut, by simp only [List.map_id]⟩
      | label => exact .frame (.pure s inner (.labelTrap _ [])) _ outer
  | frame =>
    constructor
    · intro move
      exact ⟨.done, .frame, Nested.lime_frame_result (r := .trap) move⟩
    · rintro ⟨out, step, rfl⟩
      cases step
      exact .pure s outer (.frameTrap _ inner)
  | done =>
    exact iff_of_false (fun h => Nested.lime_result_stuck (r := .trap) h) (by
      rintro ⟨out, step, _⟩
      cases step)

theorem core_trap_run_iff {H : Type} {P : Numerics.Profile} {s : Core.Store H}
    {entry : Entry} {program : CallContinuation.OuterCall.Ranked.Graph.Program} {tables : Source.Tables}
    {outer : Frame} {index : FuncIdx} {args : List Value} {active : Source.Activation}
    (ready : entry.Checked program tables outer index args active)
    (allocated : entry.CoreAllocated program tables active s) {out : Outcome}
    (resolved : active.resolve program = some out) (trap : LookupTrap out) {dst : Core.Config H} :
    Core.Steps P noHost (coreSource s outer index args) dst ↔
      dst ∈ (entry.corePrefix s outer index args active out).dropLast ∨
      ∃ phase, CleanupRuns (entry.coreTrapStart active out) phase ∧ dst = entry.coreCleanup s outer active.caller phase := by
  let before := (entry.corePrefix s outer index args active out).dropLast
  let trapped := entry.coreCleanup s outer active.caller (entry.coreTrapStart active out)
  have same : before ++ [trapped] = entry.corePrefix s outer index args active out := by
    cases trap <;>
      simp [before, trapped, Entry.corePrefix, Outcome.coreTrace, Entry.coreLookup,
        Entry.coreTrapStart, Entry.coreCleanup, Source.Activation.coreConfig, Source.coreNest,
        Indirect.coreConfig, Site.coreCode, coreValues, List.append_assoc]
  have chain : (before ++ [trapped]).IsChain (fun a b => ∀ dst, Core.Step P noHost a dst ↔ dst = b) := by
    rw [same]
    exact Core.prefix_exact ready allocated resolved
  have run := Context.Resume.prefix_run_iff (dst := dst) before trapped chain
  cases trap <;> exact run.trans (or_congr Iff.rfl (Context.finite_run_iff_of_step _ core_cleanup_step))

open Wasm.Lime1.Execution in
theorem lime_trap_run_iff {H : Type} {s : Store H}
    {entry : Entry} {program : CallContinuation.OuterCall.Ranked.Graph.Program} {tables : Source.Tables}
    {outer : Frame} {index : FuncIdx} {args : List Value} {active : Source.Activation}
    (ready : entry.Checked program tables outer index args active)
    (allocated : entry.LimeAllocated program tables active s) {out : Outcome}
    (resolved : active.resolve program = some out) (trap : LookupTrap out) {dst : Config H} :
    Steps CallFrame.limeNoHost (limeSource s outer index args) dst ↔
      dst ∈ (entry.limePrefix s outer index args active out).dropLast ∨
      ∃ phase, CleanupRuns (entry.limeTrapStart active) phase ∧ dst = entry.limeCleanup s outer active.caller phase := by
  let before := (entry.limePrefix s outer index args active out).dropLast
  let trapped := entry.limeCleanup s outer active.caller (entry.limeTrapStart active)
  have chain : (before ++ [trapped]).IsChain (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) := by
    have lookup := Lime1.prefix_exact ready allocated resolved
    cases trap <;> exact lookup
  exact (Context.Resume.prefix_run_iff (dst := dst) before trapped chain).trans
    (or_congr Iff.rfl (Context.finite_run_iff_of_step _ lime_cleanup_step))

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Proofs
