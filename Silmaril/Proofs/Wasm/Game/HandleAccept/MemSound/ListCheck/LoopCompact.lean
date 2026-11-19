module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Run.Defs
import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Replies.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Rules
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.LiveRun
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopTrace

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept
  Silmaril.Formats.Api
open Silmaril.Wasm.Game.HandleAccept.MemSound
open Silmaril.Wasm.Game.HandleAccept.MemSound.Items (itemsReply)
open Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck
open Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop
open Silmaril.Wasm.Game.HandleAccept.MemSound.Text (bytesList)
open Silmaril.Wasm.Game.HandleAccept.MemSound.Readers (symTextAns blobAns)
open Silmaril.Wasm.Game.HandleAccept.Memory (MemAtom utf8?)
open Silmaril.Wasm.Numerics Silmaril.Accept.Handle Silmaril.Formats
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

private theorem decoded_child (checker : Checker) {image : ByteArray} {bytes : List UInt8}
    {atom : MemAtom} (payload : bytesList image 0 = some bytes)
    (kind : checker.decodeBytes bytes = some atom) :
    checker.decodeChild ⟨.values [], some image⟩ 0 = .atom atom := by
  cases checker with
  | blobs =>
    unfold Checker.decodeBytes at kind
    cases kind
    simp [Checker.decodeChild, blobAns, payload]
  | symbols =>
    cases utf : utf8? bytes with
    | none => simp [Checker.decodeBytes, utf] at kind
    | some text =>
      simp only [Checker.decodeBytes, utf, Option.map_some, Option.some.injEq] at kind
      subst atom
      simp [Checker.decodeChild, symTextAns, payload, utf]

theorem bytes_accepts {profile : Profile} (checker : Checker)
    (policy : OnInvalid) {Rhos : Set (Env (BitVec 32) SymStrBytesSExp)}
    {rho : Env (BitVec 32) SymStrBytesSExp} (allowed : rho ∈ Rhos) {root : BitVec 32}
    {handles : List (BitVec 32)} (fits : 8 + 4 * handles.length ≤ 65536)
    (raw : BitVec 32 → List UInt8) (space : ∀ handle ∈ handles, 8 + (raw handle).length ≤ 65536)
    {children : List SymStrBytesSExp} (rootDenotes : rho root = some (SExp.ofList children))
    (denotes : List.Forall₂ (fun handle child => rho handle = some child) handles children)
    (atoms : ∀ handle ∈ handles, ∃ atom,
      checker.decodeBytes (raw handle) = some atom ∧ rho handle = some (.atom atom)) :
    SExp.ofList children ∈ listReaderLang profile (ReplyEnvs itemsReply) 0 (Loop.mod checker.imports)
      checker.imports checker.decodeChild .trap policy Rhos := by
  let page : ByteArray := ⟨Array.replicate 65536 0⟩
  have pageSize : page.size = 65536 := by simp only [page, ByteArray.size, Array.size_replicate]
  have width : page.size ≤ 2 ^ 32 := by rw [pageSize]; decide
  have encoded (handle : BitVec 32) (member : handle ∈ handles) :
      ∃ image, writeByteReply page (raw handle) = .ok image ∧ image.size = 65536 ∧
        bytesList image 0 = some (raw handle) := by
    obtain ⟨image, written, sameSize, read⟩ := writeByteReply_roundtrip width
      (show 8 + (raw handle).length ≤ page.size by rw [pageSize]; exact space handle member)
    exact ⟨image, written, sameSize.trans pageSize, read⟩
  let images (handle : BitVec 32) : ByteArray :=
    if member : handle ∈ handles then (encoded handle member).choose else ByteArray.empty
  have facts (handle : BitVec 32) (member : handle ∈ handles) :
      (images handle).size = 65536 ∧ bytesList (images handle) 0 = some (raw handle) := by
    simpa only [images, dite_eq_left member] using (encoded handle member).choose_spec.2
  have sizes (handle : BitVec 32) (member : handle ∈ handles) := (facts handle member).1
  obtain ⟨_, instance_, _, spec, ready⟩ := checker_instance checker
  apply checker_accepts checker spec (compact_admitted instance_.store) () ready
    (compact_plan (childBytes := images) (by decide) fits sizes checker.decodeChild)
    policy allowed rootDenotes denotes
  intro handle member
  obtain ⟨atom, meaning, named⟩ := atoms handle member
  exact ⟨atom, decoded_child checker (facts handle member).2 meaning, named⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopRun
