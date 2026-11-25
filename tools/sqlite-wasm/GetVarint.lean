module

public import SqliteWasm.ArtifactCheck
public import Silmaril.Formats.Sqlite.Varint.Defs
public import Silmaril.Wasm.Execution.Core.Properties
import SqliteWasm.GetVarintOneByte
import SqliteWasm.GetVarintTwoByte
import SqliteWasm.GetVarintThreeByte
import SqliteWasm.GetVarintFourByte
import SqliteWasm.GetVarintFiveByte
import SqliteWasm.GetVarintSixByte
import SqliteWasm.GetVarintSevenByte
import SqliteWasm.GetVarintEightByte
import SqliteWasm.GetVarintNineByte

public section

namespace SqliteWasm

open Silmaril.Formats.Sqlite
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (Expand Ty)
open SqliteWasmArtifact

private theorem memoryByte (B : ByteArray) (offset : Nat) (byte : UInt8)
    (found : (File.View.ofBytes ⟨B⟩).get? offset = some byte) :
    B[offset]? = some byte := by
  by_cases bound : offset < B.size
  · simpa [File.View.get?, File.View.ofBytes, Silmaril.Formats.Bytes.length, bound] using found
  · simp [File.View.get?, File.View.ofBytes, Silmaril.Formats.Bytes.length, bound] at found

private theorem readStep {B : ByteArray} {fuel offset accumulator : Nat} {result : Nat × Nat}
    (read : Varint.readAux? (File.View.ofBytes ⟨B⟩) (fuel + 2) offset accumulator = some result) :
    ∃ byte, B[offset]? = some byte ∧
      (byte.toNat < 128 ∨ (128 ≤ byte.toNat ∧
        Varint.readAux? (File.View.ofBytes ⟨B⟩) (fuel + 1) (offset + 1)
          (accumulator * 128 + byte.toNat % 128) = some result)) := by
  rw [Varint.readAux?] at read
  cases loaded : (File.View.ofBytes ⟨B⟩).get? offset with
  | none => simp [loaded] at read
  | some byte =>
    refine ⟨byte, memoryByte B offset byte loaded, ?_⟩
    by_cases terminal : byte.toNat < 128
    · exact Or.inl terminal
    · exact Or.inr ⟨Nat.le_of_not_gt terminal, by simpa [loaded, terminal] using read⟩

private theorem finalByte {B : ByteArray} {offset accumulator : Nat} {result : Nat × Nat}
    (read : Varint.readAux? (File.View.ofBytes ⟨B⟩) 1 offset accumulator = some result) :
    ∃ byte, B[offset]? = some byte := by
  rw [Varint.readAux?] at read
  cases loaded : (File.View.ofBytes ⟨B⟩).get? offset with
  | none => simp [loaded] at read
  | some byte => exact ⟨byte, memoryByte B offset byte loaded⟩

/-- A successful `Varint.read?` on the initial callee memory gives the exact
store and consumed length of the pinned slot-434 call, including overlapping
input and output. -/
theorem getVarint_of_read {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {caller : Frame} {fn : Func} {instanceAddr : Nat} {fi : FuncInst H}
    {src dst : BitVec 32} {memoryAddr : Nat} {mem : MemInst} {value : UInt64} {next : Nat}
    (selected : definedFunction? sqlite 434 = some fn)
    (slot : caller.module.funcs[434]? = some instanceAddr)
    (instanceAt : s.funcs[instanceAddr]? = some fi)
    (code : fi.code = .wasm fn)
    (signature : Expand fi.type (.func (.cons Ty.i32 (.cons Ty.i32 .nil)) (.cons Ty.i32 .nil)))
    (mapped : s.mem? { module := fi.module } ⟨0⟩ = some (memoryAddr, mem))
    (read : Varint.read? (File.View.ofBytes ⟨mem.bytes⟩) src.toNat = some (value, next))
    (inBounds : dst.toNat + 8 ≤ mem.bytes.size) :
    Steps P host ⟨s, caller, vals [.i32 src, .i32 dst] ++ [.plain (.call ⟨434⟩)]⟩
      ⟨s.setMem memoryAddr
        { mem with bytes := Memory.writeSlice mem.bytes dst.toNat (Memory.encodeLE 8 value.toNat) },
        caller, [constI32 (BitVec.ofNat 32 (next - src.toNat))]⟩ := by
  let effect (word width : Nat) : Prop :=
    Steps P host ⟨s, caller, vals [.i32 src, .i32 dst] ++ [.plain (.call ⟨434⟩)]⟩
      ⟨s.setMem memoryAddr
        { mem with bytes := Memory.writeSlice mem.bytes dst.toNat (Memory.encodeLE 8 word) },
        caller, [constI32 (BitVec.ofNat 32 width)]⟩
  change effect value.toNat (next - src.toNat)
  have finish {word width : Nat} (fits : word < 2 ^ 64)
      (branch :
        Varint.read? (File.View.ofBytes ⟨mem.bytes⟩) src.toNat =
          some (UInt64.ofNat word, src.toNat + width) ∧ effect word width) :
      effect value.toNat (next - src.toNat) := by
    obtain ⟨valueEq, nextEq⟩ := Prod.mk.inj (Option.some.inj (read.symm.trans branch.1))
    rw [valueEq, nextEq, UInt64.toNat_ofNat_of_lt' fits, Nat.add_sub_cancel_left]
    exact branch.2
  cases initial : Varint.readNat? (File.View.ofBytes ⟨mem.bytes⟩) src.toNat with
  | none => simp [Varint.read?, initial] at read
  | some result =>
    have path : Varint.readAux? (File.View.ofBytes ⟨mem.bytes⟩) 9 src.toNat 0 = some result := initial
    rcases readStep path with ⟨byte1, load1, stop | ⟨continue1, path⟩⟩
    · refine finish ?_ (getVarint_oneByte selected slot instanceAt code signature mapped
        load1  stop inBounds)
      omega
    rcases readStep path with ⟨byte2, load2, stop | ⟨continue2, path⟩⟩
    · refine finish ?_ (getVarint_twoByte selected slot instanceAt code signature mapped
        load1 load2 continue1 stop inBounds)
      omega
    rcases readStep path with ⟨byte3, load3, stop | ⟨continue3, path⟩⟩
    · refine finish ?_ (getVarint_threeByte selected slot instanceAt code signature mapped
        load1 load2 load3 continue1 continue2 stop inBounds)
      omega
    rcases readStep path with ⟨byte4, load4, stop | ⟨continue4, path⟩⟩
    · refine finish ?_ (getVarint_fourByte selected slot instanceAt code signature mapped
        load1 load2 load3 load4 continue1 continue2 continue3 stop inBounds)
      omega
    rcases readStep path with ⟨byte5, load5, stop | ⟨continue5, path⟩⟩
    · refine finish ?_ (getVarint_fiveByte selected slot instanceAt code signature mapped
        load1 load2 load3 load4 load5 continue1 continue2 continue3 continue4 stop inBounds)
      omega
    rcases readStep path with ⟨byte6, load6, stop | ⟨continue6, path⟩⟩
    · refine finish ?_ (getVarint_sixByte selected slot instanceAt code signature mapped
        load1 load2 load3 load4 load5 load6 continue1 continue2 continue3 continue4 continue5 stop inBounds)
      omega
    rcases readStep path with ⟨byte7, load7, stop | ⟨continue7, path⟩⟩
    · refine finish ?_ (getVarint_sevenByte selected slot instanceAt code signature mapped
        load1 load2 load3 load4 load5 load6 load7 continue1 continue2 continue3 continue4 continue5 continue6 stop inBounds)
      omega
    rcases readStep path with ⟨byte8, load8, stop | ⟨continue8, path⟩⟩
    · refine finish ?_ (getVarint_eightByte selected slot instanceAt code signature mapped
        load1 load2 load3 load4 load5 load6 load7 load8 continue1 continue2 continue3 continue4 continue5 continue6 continue7 stop inBounds)
      omega
    obtain ⟨byte9, load9⟩ := finalByte path
    have byteBound := byte9.toNat_lt
    refine finish ?_ (getVarint_nineByte selected slot instanceAt code signature mapped
      load1 load2 load3 load4 load5 load6 load7 load8 load9 continue1 continue2 continue3 continue4 continue5 continue6 continue7 continue8 inBounds)
    omega

#print axioms getVarint_of_read

end SqliteWasm
