module

import Silmaril.X86.Concurrency.Sqlite.Defs

namespace Silmaril.X86.Concurrency.Sqlite

open Silmaril.Machine.SqliteControl (Config Phase Shared)
open Silmaril.X86.MemoryModel.Tso (XEvent XState enqueue writeMem xembed)

private def hiddenStore : XEvent Nat := .store 0 4 [1, 2]
private def labels := [hiddenStore]
private def initial : MemoryModel.Tso.Mem := fun _ => some 0
private def control : Config Phase := ⟨{}, fun _ => .idle⟩

private def hideStore (Final : Type) : Projection .control (XEvent Nat) Final where
  event := fun _ => none
  final := fun _ => ({} : Shared)

private theorem coversBoth {Input Final : Type}
    {runs : Input → Set (ImplementationRun (XEvent Nat) Final)} {start : Input} {finish : Final}
    {allowed : Set Nat}
    (run : ⟨labels, finish, issuedBytes labels⟩ ∈ runs start)
    (sound : Sound runs (hideStore Final) (fun _ _ => allowed) {(start, control)}) :
    4 ∈ allowed ∧ 5 ∈ allowed := by
  have coverage := (sound (start, control) rfl _ run).2
  exact ⟨coverage ⟨hiddenStore, List.mem_cons_self, (show 4 ≤ 4 ∧ 4 < 6 by decide)⟩,
    coverage ⟨hiddenStore, List.mem_cons_self, (show 4 ≤ 5 ∧ 5 < 6 by decide)⟩⟩

private theorem scRun :
    ⟨labels, writeMem initial 4 [1, 2], issuedBytes labels⟩ ∈ scRuns Set.univ initial :=
  ⟨trivial, .cons (.store _ _ _ _) (.nil _), rfl⟩

/-- The store stays pending. Its span is covered at issue even though memory is unchanged. -/
private theorem tsoRun :
    ⟨labels, enqueue (xembed initial) 0 4 [1, 2], issuedBytes labels⟩ ∈
      tsoRuns Set.univ (xembed initial) :=
  ⟨trivial, .cons ⟨_, _, .refl, .store _ _ _ _, .refl⟩ (.nil _), rfl⟩

example : ¬Sound (scRuns Set.univ) (hideStore MemoryModel.Tso.Mem) (fun _ _ => ∅) {(initial, control)} :=
  fun h => (coversBoth scRun h).1

example : ¬Sound (scRuns Set.univ) (hideStore MemoryModel.Tso.Mem) (fun _ _ => {4}) {(initial, control)} :=
  fun h => (by decide : (5 : Nat) ≠ 4) (coversBoth scRun h).2

example :
    ¬Sound (tsoRuns Set.univ) (hideStore (XState Nat)) (fun _ _ => ∅) {(xembed initial, control)} :=
  fun h => (coversBoth tsoRun h).1

example :
    ¬Sound (tsoRuns Set.univ) (hideStore (XState Nat)) (fun _ _ => {4}) {(xembed initial, control)} :=
  fun h => (by decide : (5 : Nat) ≠ 4) (coversBoth tsoRun h).2

private theorem chosenTraces {α : Type} {actual chosen : List α}
    (h : List.Forall₂ (· ∈ ·) actual (chosen.map fun item => [item])) : actual = chosen := by
  induction chosen generalizing actual with
  | nil => cases h; rfl
  | cons item rest ih =>
    cases h with
    | cons first tail => rw [List.mem_singleton.mp first, ih tail]

/-- The footprint is an envelope of the actual checked candidate's units. -/
example {model : MemoryModel.Lattice.Name} {test : MemoryModel.Litmus.Test}
    {choices : List (List MemoryModel.Litmus.XTrace)}
    {run : ImplementationRun MemoryModel.Litmus.XTrace MemoryModel.Litmus.Final}
    (h : run ∈ axiomaticRuns model test choices) :
    ∃ x : MemoryModel.Axiomatic.Exec,
      run.bytes = { addr | ∃ unit ∈ x.evs, (unit.isR || unit.isW) = true ∧ unit.covers addr = true } := by
  obtain ⟨_, ⟨actual, actualOk, x, events, _, _, _, _, _⟩, bytes⟩ := h
  have eq := chosenTraces actualOk
  subst actual
  exact ⟨x, by rw [bytes, events]; rfl⟩

end Silmaril.X86.Concurrency.Sqlite
