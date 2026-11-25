module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Control.Defs
import Silmaril.X86.Concurrency.Sqlite.Release.Thms

public section

namespace Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Control

open Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock
open Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Control
open Silmaril.X86.Ext (leBytes)
open Silmaril.X86.Concurrency.Sqlite
open Silmaril.X86.Concurrency.Sqlite.Release (BuffersAvoid dword_release releaseInput releasedView)
open Silmaril.X86.MemoryModel.Tso hiding Execution
open Silmaril.X86.MemoryModel
open Silmaril.Machine.SqliteControl

private theorem flush_avoids {initial final : XState Nat} {address : Nat}
    (steps : XFlushes initial final) (safe : BuffersAvoid initial address) :
    BuffersAvoid final address := by
  induction steps with
  | refl => exact safe
  | tail _ edge ih =>
    cases edge with
    | head actor base bytes rest oldest =>
      intro tid entry member
      by_cases same : tid = actor
      · subst tid
        apply ih actor entry
        rw [oldest]
        exact List.mem_cons_of_mem _ (by simpa using member)
      · exact ih tid entry (by simpa [Function.update_of_ne same] using member)

private def storeAvoids (address : Nat) : XEvent Nat → Prop
  | .store _ base bytes => entryByte base bytes address = none
  | _ => True

private theorem step_avoids {initial final : XState Nat} {event : XEvent Nat} {address : Nat}
    (edge : XWeakStep initial event final) (safe : BuffersAvoid initial address)
    (storeSafe : storeAvoids address event) : BuffersAvoid final address := by
  obtain ⟨_, _, before, issued, after⟩ := edge
  apply flush_avoids after
  have safeBefore := flush_avoids before safe
  cases issued with
  | load => exact safeBefore
  | rmw => exact safeBefore
  | fence => exact safeBefore
  | store actor base bytes =>
    intro tid entry member
    by_cases same : tid = actor
    · subst tid
      simp only [enqueue, Function.update_self, List.mem_append, List.mem_singleton] at member
      rcases member with old | rfl
      · exact safeBefore actor entry old
      · exact storeSafe
    · exact safeBefore tid entry (by simpa [enqueue, Function.update_of_ne same] using member)

private theorem prefix_exchange {initial final : XState Nat} {events : List (XEvent Nat)}
    {endEvent : XEvent Nat} {base : Nat}
    (path : Tso.Execution XWeakStep initial (events ++ [endEvent]) final)
    (safe : ∀ address, base ≤ address → address < base + 4 → BuffersAvoid initial address)
    (each : ∀ event ∈ events, ∀ address, base ≤ address → address < base + 4 →
      storeAvoids address event) :
    ∃ before, (∀ address, base ≤ address → address < base + 4 → BuffersAvoid before address) ∧
      XWeakStep before endEvent final := by
  induction events generalizing initial with
  | nil =>
    cases path with
    | cons edge tail => cases tail; exact ⟨_, safe, edge⟩
  | cons event events ih =>
    cases path with
    | cons edge tail =>
      exact ih tail
        (fun address low high => step_avoids edge (safe address low high)
          (each event (List.mem_cons_self) address low high))
        (fun next member => each next (List.mem_cons_of_mem _ member))

private def preExchange (tid base : Nat) (users kind : BitVec 32) : List (XEvent Nat) :=
  (FifoData.dataEvents tid base users kind).take 7

private theorem data_events_split (tid base : Nat) (users kind : BitVec 32) :
    FifoData.dataEvents tid base users kind = preExchange tid base users kind ++ [exchange tid base] :=
  rfl

private theorem data_run_lock {initial final : XState Nat} {tid base : Nat} {users kind : BitVec 32}
    (safe : ∀ address, base ≤ address → address < base + 4 → BuffersAvoid initial address)
    (path : Tso.Execution XWeakStep initial (FifoData.dataEvents tid base users kind) final) :
    ∀ address, base ≤ address → address < base + 4 → final.memory address = some 0 := by
  rw [data_events_split] at path
  have storesSafe : ∀ event ∈ preExchange tid base users kind, ∀ address,
      base ≤ address → address < base + 4 → storeAvoids address event := by
    intro event member address _ high
    simp only [preExchange, FifoData.dataEvents, List.take_succ_cons, List.take_zero,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [storeAvoids, entryByte, show ¬ base + 4 ≤ address by omega,
        show ¬ base + 8 ≤ address by omega, show ¬ base + 12 ≤ address by omega]
  obtain ⟨_, avoids, edge⟩ := prefix_exchange path safe storesSafe
  exact (dword_release avoids edge).1

theorem issued_bytes (tid base : Nat) (users kind : BitVec 32) :
    issuedBytes (FifoData.dataEvents tid base users kind) = footprint base := by
  ext address
  simp [issuedBytes, FifoData.dataEvents, accessBytes, footprint, FifoData.zeroDword,
    FifoData.usersDword, leBytes]
  omega

theorem confined_sound (tid base : Nat) (busy rc : Int32) (users kind : BitVec 32) :
    Sound .fifo id (fun _ run => run.labels = FifoData.dataEvents tid base users kind)
      (projection tid base busy) (fun _ _ => footprint base)
      (confined tid base busy rc) := by
  rintro ⟨initial, spec⟩ pair ⟨events, last⟩ path selected
  obtain ⟨safe, _, same⟩ : (∀ address, base ≤ address → address < base + 4 →
      BuffersAvoid initial address) ∧ readMem initial.memory base 4 = some [1, 0, 0, 0] ∧
      spec = releaseInput tid busy rc := pair
  subst spec
  change events = FifoData.dataEvents tid base users kind at selected
  subst events
  have zero : last.memory base = some 0 :=
    data_run_lock safe path base (Nat.le_refl _) (by omega)
  constructor
  · change (projection tid base busy).observe (model := .fifo)
      ⟨FifoData.dataEvents tid base users kind, last⟩ ∈
      Layer.behaviors .control (releaseInput tid busy rc)
    have observed : (projection tid base busy).observe (model := .fifo)
        ⟨FifoData.dataEvents tid base users kind, last⟩ =
        (([Event.released tid], ⟨none, busy⟩) : Layer.control.Observation) := by
      apply Prod.ext
      · let emit := (projection tid base busy).event
        change List.filterMap emit (FifoData.dataEvents tid base users kind) = [Event.released tid]
        have before : List.filterMap emit (preExchange tid base users kind) = [] := rfl
        have lastEvent : emit (exchange tid base) = some (.released tid) := by
          simp [emit, projection, exchange]
        rw [data_events_split, List.filterMap_append, before, List.nil_append,
          List.filterMap_cons_some lastEvent, List.filterMap_nil]
        rfl
      · change releasedView tid base busy last.memory = _
        simp [releasedView, zero]
    rw [observed]
    let initialVM := releaseInput tid busy rc
    let finalVM := initialVM.advance tid (.returnResult rc) ⟨none, busy⟩
    have stepReleases : Step initialVM (some (.released tid)) finalVM := by
      exact ⟨tid, .tick, _, rfl, by simp [step, initialVM, finalVM, releaseInput]⟩
    exact ⟨finalVM, .more stepReleases (.done finalVM), rfl⟩
  · change issuedBytes (FifoData.dataEvents tid base users kind) ⊆ footprint base
    rw [issued_bytes]

end Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Control
