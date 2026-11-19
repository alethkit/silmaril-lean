module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Run.Defs
import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Replies.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Rules
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.LiveRun

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept
  Silmaril.Formats.Api
open Silmaril.Wasm.Game.HandleAccept.MemSound
open Silmaril.Wasm.Game.HandleAccept.MemSound.Items (itemsReply)
open Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck
open Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop
open Silmaril.Wasm.Game.HandleAccept.Memory (MemAtom)
open Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound (setMem_mems memOf_setMem)

theorem checker_instance (checker : Checker) :
    ∃ mt instance_ initial, IsSpecInstance (Loop.mod checker.imports) mt instance_ initial ∧
      ReplySpace 65536 initial.store := by
  have valid : (Silmaril.Wasm.Verify.specInstance? (Loop.mod checker.imports)).isSome = true := by
    cases checker <;> decide +kernel
  have page : Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.memSizes (Loop.mod checker.imports) =
      [65536] := by
    cases checker <;> decide +kernel
  obtain ⟨mt, instance_, initial, spec⟩ := Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.spec_exists valid
  obtain ⟨cfg, start, prepared, rfl, _, _⟩ :=
    Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.prep_of_spec spec
  have space := Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.one_page page prepared
  exact ⟨mt, instance_, cfg.withStart start, spec, by cases start <;> exact space⟩

theorem compact_admitted {handles : List (BitVec 32)} {childBytes : BitVec 32 → ByteArray}
    (store : Store Nat) : ReplyEnvs itemsReply store (compactHost handles childBytes) := by
  intro state call reply next answer
  change CompactReply handles childBytes call reply at answer
  cases answer <;> simp [itemsReply, ShapedReply, KeepsCode, Store.setMem]

theorem compact_plan {capacity : Nat} (width : capacity ≤ 2 ^ 32)
    {root : BitVec 32} {handles : List (BitVec 32)} (fits : 8 + 4 * handles.length ≤ capacity)
    {childBytes : BitVec 32 → ByteArray}
    (childFits : ∀ handle ∈ handles, (childBytes handle).size = capacity)
    (decode : HostReply → BitVec 32 → SxA MemAtom (BitVec 32)) :
    ReplyPlan (compactHost handles childBytes) (ReplySpace capacity) decode root handles
      (fun handle => decode ⟨.values [], some (childBytes handle)⟩ 0) := by
  constructor
  · intro store state ready
    obtain ⟨mem, atMemory, size⟩ := ready
    obtain ⟨bytes, written, sameSize, decoded, _⟩ :=
      writeItemsReply_roundtrip (memory := mem.bytes) (handles := handles) (size.symm ▸ width) (size.symm ▸ fits)
    let newMem : MemInst := { mem with bytes }
    have memLen : store.mems.length = 1 := by rw [atMemory]; rfl
    have facts := setMem_mems (mi := newMem) memLen
    refine ⟨store.setMem 0 newMem, (), newMem, CompactReply.items atMemory written,
      ⟨newMem, ?_, sameSize.trans size⟩, facts.2.2, facts.1, decoded, ?_⟩
    · simp [Store.setMem, atMemory, newMem]
    · exact (sameSize.trans size).symm ▸ width
  · intro handle member store state ready
    obtain ⟨mem, atMemory, _⟩ := ready
    let newMem : MemInst := { mem with bytes := childBytes handle }
    have memLen : store.mems.length = 1 := by rw [atMemory]; rfl
    have facts := setMem_mems (mi := newMem) memLen
    refine ⟨store.setMem 0 newMem, (), CompactReply.child atMemory member,
      ⟨newMem, ?_, childFits handle member⟩, facts.2.2, ?_⟩
    · simp [Store.setMem, atMemory, newMem]
    · rw [memOf_setMem memLen]

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopRun
