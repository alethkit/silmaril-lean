module

public import SqliteWasm.DirectPreparation
public import SqliteWasm.GetVarint
import SqliteWasm.PreparedVarintRoundtrip
import SqliteWasm.PreparedVarintTwoByteRoundtrip
import SqliteWasm.PreparedVarintOrdinaryRoundtrip
import SqliteWasm.PreparedVarintNineByteRoundtrip
import SqliteWasm.PutVarintCheck
import SqliteWasm.PutVarintTwoByte
import SqliteWasm.NineByteVarint
import SqliteWasm.OrdinaryVarintMemory

public section

namespace SqliteWasm

open Silmaril.Formats.Sqlite
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

private theorem agreeOnPreparation
    {runtime otherStore : Store Nat} {frame otherFrame : Frame}
    {address otherAddress : Nat} {mem otherMem : MemInst}
    (prepared : prepareDirect? evalConst? reactorTypedImports sqlite reactorImportAddrs =
      some (runtime, frame, none))
    (otherPrepared : prepareDirect? evalConst? reactorTypedImports sqlite reactorImportAddrs =
      some (otherStore, otherFrame, none))
    (mapped : runtime.mem? frame ⟨0⟩ = some (address, mem))
    (otherMapped : otherStore.mem? otherFrame ⟨0⟩ = some (otherAddress, otherMem)) :
    otherStore = runtime ∧ otherFrame = frame ∧ otherAddress = address ∧ otherMem = mem := by
  obtain ⟨stores, frames⟩ := Prod.mk.inj (Option.some.inj (otherPrepared.symm.trans prepared))
  obtain ⟨sameFrame, _⟩ := Prod.mk.inj frames
  subst otherStore
  subst otherFrame
  exact ⟨rfl, rfl, Prod.mk.inj (Option.some.inj (otherMapped.symm.trans mapped))⟩

/-- All encoded widths in the canonical prepared reactor, with each branch's
address and scratch bounds made explicit. -/
theorem reactorPreparedVarintRoundtrip (P : Profile) (host : HostSemantics Nat) :
    ∃ runtime frame mem address,
      prepareDirect? evalConst? reactorTypedImports sqlite reactorImportAddrs =
        some (runtime, frame, none) ∧
      runtime.mem? frame ⟨0⟩ = some (address, mem) ∧ mem.bytes.size = 131072 ∧
      ∀ (ptr : BitVec 32) (value : UInt64),
        let width := (Varint.encode value).length
        ptr.toNat + max 8 width ≤ mem.bytes.size →
        (16384 ≤ value.toNat → value.toNat < 2 ^ 56 →
          ptr.toNat + width ≤ 126102 ∨ 126102 + width ≤ ptr.toNat) →
        let scratch := if 16384 ≤ value.toNat ∧ value.toNat < 2 ^ 56 then
          Memory.writeSlice mem.bytes 126102 ⟨⟨(Varint.encode value).toList.reverse⟩⟩
          else mem.bytes
        let written := Memory.writeSlice scratch ptr.toNat (Varint.encode value).data
        let final := Memory.writeSlice written ptr.toNat (Memory.encodeLE 8 value.toNat)
        Varint.read? (File.View.ofBytes ⟨written⟩) ptr.toNat = some (value, ptr.toNat + width) ∧
        Steps P host
          ⟨runtime, frame, vals [.i32 ptr, .i64 value.toBitVec] ++ [.plain (.call ⟨530⟩)] ++
            vals [.i32 ptr, .i32 ptr] ++ [.plain (.call ⟨434⟩)]⟩
          ⟨runtime.setMem address { mem with bytes := final }, frame,
            vals [.i32 (BitVec.ofNat 32 width), .i32 (BitVec.ofNat 32 width)]⟩ := by
  obtain ⟨runtime, frame, mem, address, prepared, mapped, size, one⟩ :=
    reactorPreparedOneByteRoundtrip P host
  refine ⟨runtime, frame, mem, address, prepared, mapped, size, ?_⟩
  intro ptr value
  dsimp only
  intro fits disjoint
  have destFits : ptr.toNat + 8 ≤ mem.bytes.size := by
    have h := Nat.le_max_left 8 (Varint.encode value).length
    omega
  by_cases small : value.toNat < 128
  · have noScratch : ¬ (16384 ≤ value.toNat ∧ value.toNat < 2 ^ 56) := by omega
    have length : (Varint.encode value).length = 1 := by simp [encode_one_byte value small]
    rw [ite_eq_right noScratch, length]
    exact one ptr value small destFits
  by_cases twoBytes : value.toNat < 16384
  · obtain ⟨other, fr, mi, addr, p, m, _, two⟩ := reactorPreparedTwoByteRoundtrip P host
    obtain ⟨stores, frames, addresses, memories⟩ := agreeOnPreparation prepared p mapped m
    subst other
    subst fr
    subst addr
    subst mi
    have lower : 128 ≤ value.toNat := by omega
    have noScratch : ¬ (16384 ≤ value.toNat ∧ value.toNat < 2 ^ 56) := by omega
    have length : (Varint.encode value).length = 2 := by simp [encode_two value lower twoBytes]
    rw [ite_eq_right noScratch, length]
    exact two ptr value lower twoBytes destFits
  by_cases ordinary : value.toNat < 2 ^ 56
  · obtain ⟨other, fr, mi, addr, p, m, _, normal⟩ := reactorPreparedOrdinaryRoundtrip P host
    obtain ⟨stores, frames, addresses, memories⟩ := agreeOnPreparation prepared p mapped m
    subst other
    subst fr
    subst addr
    subst mi
    have lower : 16384 ≤ value.toNat := by omega
    obtain ⟨width, entered, valid⟩ := OrdinaryVarint.existsWidth value.toNat lower ordinary
    have length : (Varint.encode value).length = width :=
      OrdinaryVarint.ordinaryLength value width valid
    have separate := disjoint lower ordinary
    rw [length] at separate
    have usesScratch : 16384 ≤ value.toNat ∧ value.toNat < 2 ^ 56 := ⟨lower, ordinary⟩
    rw [ite_eq_left usesScratch, length]
    exact normal ptr value width entered valid.ordinary valid.lower valid.upper destFits separate
  · obtain ⟨other, fr, mi, addr, p, m, _, nine⟩ := reactorPreparedNineByteRoundtrip P host
    obtain ⟨stores, frames, addresses, memories⟩ := agreeOnPreparation prepared p mapped m
    subst other
    subst fr
    subst addr
    subst mi
    have high : 2 ^ 56 ≤ value.toNat := by omega
    have noScratch : ¬ (16384 ≤ value.toNat ∧ value.toNat < 2 ^ 56) := by omega
    have length := NineByteVarint.encodedLength value high
    have writerFits : ptr.toNat + 9 ≤ mem.bytes.size := by simpa [length] using fits
    rw [ite_eq_right noScratch, length]
    exact nine ptr value high writerFits

#print axioms reactorPreparedVarintRoundtrip

end SqliteWasm
