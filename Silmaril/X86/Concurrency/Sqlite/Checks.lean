module

import Silmaril.X86.Concurrency.Sqlite.Defs

namespace Silmaril.X86.Concurrency.Sqlite

open Silmaril.Machine.SqliteControl (Config Phase Shared)
open Silmaril.X86.MemoryModel.Tso (XEvent enqueue writeMem xembed)

private def hiddenStore : XEvent Nat := .store 0 4 [1, 2]
private def initial : MemoryModel.Tso.Mem := fun _ => some 0
private def control : Config Phase := ⟨{}, fun _ => .idle⟩

private def hideStore (Final : Type) : Projection .control (XEvent Nat) Final where
  event := fun _ => none
  final := fun _ => ({} : Shared)

private theorem scRun :
    MemorySemantics.sc.Executes initial ⟨[hiddenStore], writeMem initial 4 [1, 2]⟩ :=
  .cons (.store _ _ _ _) (.nil _)

/-- The store stays pending. Its span is covered at issue even though memory is unchanged. -/
private theorem tsoRun :
    MemorySemantics.fifo.Executes (xembed initial) ⟨[hiddenStore], enqueue (xembed initial) 0 4 [1, 2]⟩ :=
  .cons ⟨_, _, .refl, .store _ _ _ _, .refl⟩ (.nil _)

private theorem firstByte :
    4 ∈ issuedBytes [hiddenStore] :=
  ⟨hiddenStore, List.mem_cons_self, (show 4 ≤ 4 ∧ 4 < 6 by decide)⟩

private theorem secondByte :
    5 ∈ issuedBytes [hiddenStore] :=
  ⟨hiddenStore, List.mem_cons_self, (show 4 ≤ 5 ∧ 5 < 6 by decide)⟩

/-- Exercise the public judgment directly with an explicit admission predicate. -/
example :
    ¬Sound .sc id (fun _ run => run.labels = [hiddenStore]) (hideStore _)
      (fun _ _ => ∅) {(initial, control)} :=
  fun sound => (sound (initial, control) rfl _ scRun rfl).2 firstByte

example :
    ¬Sound .sc id (fun _ run => run.labels = [hiddenStore]) (hideStore _)
      (fun _ _ => {4}) {(initial, control)} :=
  fun sound => (by decide : (5 : Nat) ≠ 4) ((sound (initial, control) rfl _ scRun rfl).2 secondByte)

example :
    ¬Sound .fifo id (fun _ run => run.labels = [hiddenStore]) (hideStore _)
      (fun _ _ => ∅) {(xembed initial, control)} :=
  fun sound => (sound (xembed initial, control) rfl _ tsoRun rfl).2 firstByte

example :
    ¬Sound .fifo id (fun _ run => run.labels = [hiddenStore]) (hideStore _)
      (fun _ _ => {4}) {(xembed initial, control)} :=
  fun sound => (by decide : (5 : Nat) ≠ 4) ((sound (xembed initial, control) rfl _ tsoRun rfl).2 secondByte)

private theorem chosenTraces {α : Type} {actual chosen : List α}
    (h : List.Forall₂ (· ∈ ·) actual (chosen.map fun item => [item])) : actual = chosen := by
  induction chosen generalizing actual with
  | nil => cases h; rfl
  | cons item rest ih =>
    cases h with
    | cons first tail => rw [List.mem_singleton.mp first, ih tail]

/-- The footprint is the set of bytes touched by the actual checked candidate's units. -/
example {model : MemoryModel.Lattice.Name} {test : MemoryModel.Litmus.Test}
    {run : Execution (.axiomatic model)} (h : (MemorySemantics.axiomatic model).Executes test run) :
    ∃ x : MemoryModel.Axiomatic.Exec, x.Wf = true ∧ model.model x ∧
      run.bytes = { addr | ∃ unit ∈ x.evs, (unit.isR || unit.isW) = true ∧ unit.covers addr = true } := by
  obtain ⟨actual, actualOk, x, events, _, wellFormed, _, consistent, _⟩ := h
  have eq := chosenTraces actualOk
  subst actual
  exact ⟨x, wellFormed, consistent, by rw [events]; rfl⟩

end Silmaril.X86.Concurrency.Sqlite
