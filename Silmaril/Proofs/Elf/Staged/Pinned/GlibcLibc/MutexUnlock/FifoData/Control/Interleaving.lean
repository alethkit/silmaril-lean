module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Control.Interleaving.Defs
import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Control.Thms
import Silmaril.X86.Concurrency.Sqlite.Release.Thms

public section

namespace Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Control.Interleaving

open Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock
open Silmaril.X86.Concurrency.Sqlite
open Silmaril.X86.Concurrency.Sqlite.Release
open Silmaril.X86.MemoryModel.Tso hiding Execution
open Silmaril.X86.MemoryModel
open Silmaril.Machine.SqliteControl
open Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Control.Interleaving (admitted)

private theorem pinned_release_byte {initial final : XState Nat} {events : List (XEvent Nat)}
    {tid base address : Nat} {users kind : BitVec 32}
    (path : Tso.Execution XWeakStep initial events final)
    (issuer : events.filter (fun event => event.thread == tid) = FifoData.dataEvents tid base users kind)
    (confined : PeerBuffersAvoid initial tid address)
    (disjoint : ∀ event ∈ events, event.thread ≠ tid → byteEffect event address none = none) :
    final.buffer tid = [] ∧
      final.memory address = writeMem (FifoData.committedStores (viewMem initial tid) base users)
        base FifoData.zeroDword address := by
  have last : (events.filter (fun event => event.thread == tid)).getLast? =
      some (.rmw tid base [1, 0, 0, 0] FifoData.zeroDword) := by rw [issuer]; rfl
  obtain ⟨empty, backing⟩ := interleaving_last_rmw_backing path confined disjoint last
  refine ⟨empty, ?_⟩
  rw [issuer] at backing
  exact backing

theorem released_lock {initial final : XState Nat} {events : List (XEvent Nat)}
    {tid base : Nat} {users kind : BitVec 32}
    (path : Tso.Execution XWeakStep initial events final)
    (issuer : events.filter (fun event => event.thread == tid) = FifoData.dataEvents tid base users kind)
    (initiallyConfined : ∀ address, base ≤ address → address < base + 4 →
      PeerBuffersAvoid initial tid address)
    (issuedConfined : ∀ event ∈ events, event.thread ≠ tid →
      ∀ address, base ≤ address → address < base + 4 → byteEffect event address none = none) :
    final.buffer tid = [] ∧ ∀ address, base ≤ address → address < base + 4 →
      final.memory address = some 0 := by
  have release (address : Nat) (low : base ≤ address) (high : address < base + 4) :=
    pinned_release_byte path issuer (initiallyConfined address low high)
      (fun event member peer => issuedConfined event member peer address low high)
  refine ⟨(release base (Nat.le_refl _) (by omega)).1, ?_⟩
  intro address low high
  rw [(release address low high).2, writeMem, entryByte]
  have offset : address - base = 0 ∨ address - base = 1 ∨ address - base = 2 ∨ address - base = 3 :=
    by omega
  rcases offset with o | o | o | o <;> simp [low, FifoData.zeroDword, o]

private theorem filterMap_issuer {α : Type} (emit : XEvent Nat → Option α)
    (tid : Nat) (events : List (XEvent Nat))
    (silent : ∀ event, event.thread ≠ tid → emit event = none) :
    events.filterMap emit = (events.filter (fun event => event.thread == tid)).filterMap emit := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
    by_cases own : event.thread = tid
    · simp [own, List.filterMap_cons, ih]
    · simp [beq_eq_false_iff_ne.mpr own, silent event own, ih]

theorem confined_sound (tid base : Nat) (busy rc : Int32)
    (users kind : BitVec 32) (peerBytes : Set Nat) :
    Sound .fifo id (admitted tid base users kind peerBytes)
      (FifoData.Control.projection tid base busy)
      (fun _ _ => FifoData.Control.footprint base ∪ peerBytes)
      (FifoData.Control.confined tid base busy rc) := by
  rintro ⟨initial, spec⟩ pair ⟨events, final⟩ path ⟨issuer, peers⟩
  change List (XEvent Nat) at events
  change XState Nat at final
  obtain ⟨safe, _, same⟩ : (∀ address, base ≤ address → address < base + 4 →
      BuffersAvoid initial address) ∧ readMem initial.memory base 4 = some [1, 0, 0, 0] ∧
      spec = releaseInput tid busy rc := pair
  subst spec
  change events.filter (fun event => event.thread == tid) =
    FifoData.dataEvents tid base users kind at issuer
  have lock := released_lock path issuer
    (fun address low high peer _ => safe address low high peer)
    (fun event member peer => (peers event member peer).2)
  have zero : final.memory base = some 0 := lock.2 base (Nat.le_refl _) (by omega)
  let proj := FifoData.Control.projection tid base busy
  have silent : ∀ event, event.thread ≠ tid → proj.event event = none := by
    intro event peer
    cases event with
    | load | store | fence => rfl
    | rmw actor addr old new =>
      have neq : XEvent.rmw actor addr old new ≠ FifoData.Control.exchange tid base := by
        intro same
        exact peer (congrArg XEvent.thread same)
      change (if XEvent.rmw actor addr old new = FifoData.Control.exchange tid base
        then some (Event.released tid) else none) = none
      simp [neq]
  constructor
  · change proj.observe (model := .fifo) ⟨events, final⟩ ∈
      Layer.behaviors .control (releaseInput tid busy rc)
    have obs : proj.observe (model := .fifo) ⟨events, final⟩ =
        (([Event.released tid], ⟨none, busy⟩) : Layer.control.Observation) := by
      apply Prod.ext
      · change events.filterMap proj.event = [.released tid]
        rw [filterMap_issuer proj.event tid events silent, issuer]
        simp [FifoData.dataEvents, proj, FifoData.Control.projection, FifoData.Control.exchange, List.filterMap_cons]
      · change releasedView tid base busy final.memory = _
        simp [releasedView, zero]
    rw [obs]
    let init := releaseInput tid busy rc
    let after := init.advance tid (.returnResult rc) ⟨none, busy⟩
    have edge : Step init (some (.released tid)) after := by
      exact ⟨tid, .tick, _, rfl, by simp [step, init, after, releaseInput]⟩
    exact ⟨after, .more edge (.done after), rfl⟩
  · change issuedBytes events ⊆ FifoData.Control.footprint base ∪ peerBytes
    rintro address ⟨event, member, access⟩
    by_cases own : event.thread = tid
    · left
      rw [← FifoData.Control.issued_bytes tid base users kind, ← issuer]
      exact ⟨event, List.mem_filter.mpr ⟨member, beq_iff_eq.mpr own⟩, access⟩
    · exact Or.inr ((peers event member own).1 access)

end Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Control.Interleaving
