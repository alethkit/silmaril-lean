module

import SqliteWasm.PreparedNullDbCheck
import SqliteWasm.ArtifactCheck
import Silmaril.Wasm.Verify.Kernel.Defs

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (DefType)
open SqliteWasmArtifact

set_option maxRecDepth 65536

sqlite_check_eq originalNullDbCheck : sourceFunction? original 130 = definedFunction? sqlite 130

theorem decodedNullDbCheckAndLogger :
    (Binary.Core.decode? originalBytes.toByteArray).map
      (fun m => (definedFunction? m 130, definedFunction? m 26)) =
        some (definedFunction? sqlite 130, definedFunction? sqlite 26) := by
  rw [originalDecode, Option.map_some]

private def check : Func := (definedFunction? sqlite 130).get (by kernel_rfl)
private def logger : Func := (definedFunction? sqlite 26).get (by kernel_rfl)
private def checkType : DefType := ((allocTypes sqlite.types)[check.type.toNat]?).get (by kernel_rfl)
private def loggerType : DefType := ((allocTypes sqlite.types)[logger.type.toNat]?).get (by kernel_rfl)

private def linked : ModuleInst :=
  { funcs := (List.replicate 131 0).set 26 1, globals := [0], mems := [0] }

private def caller : Frame := { module := linked, locals := [some (.i64 43)] }
private def memory : MemInst := ⟨⟨.i32, ⟨1, none⟩⟩, ⟨Array.replicate 65536 0⟩⟩

private def initial (sp : BitVec 32) : Store Nat :=
  { funcs := [⟨checkType, linked, .wasm check⟩, ⟨loggerType, linked, .wasm logger⟩]
    mems := [memory]
    globals := [⟨⟨.var, .i32⟩, .i32 sp⟩, ⟨⟨.var, .i32⟩, .i32 17⟩] }

private theorem fixtureZero : Memory.load memory.bytes 52996 4 = some 0 := by
  have size : memory.bytes.size = 65536 := Array.size_replicate
  have read : memory.bytes.extract 52996 53000 = ⟨Array.replicate 4 0⟩ := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    change (Array.replicate 65536 (0 : UInt8)).extract 52996 53000 = Array.replicate 4 0
    rw [Array.extract_replicate]
    rfl
  unfold Memory.load Memory.readBytes
  rw [size, ite_eq_left (by decide : 52996 + 4 ≤ 65536), read]
  rfl

private def diagnosticWord : ByteArray := ⟨#[0x33, 0x4a, 0, 0]⟩

private theorem fixture (P : Profile) (host : HostSemantics Nat) (sp : BitVec 32)
    (fits : (sp - 16#32).toNat + 4 ≤ 65536)
    (disjoint : 52996 + 4 ≤ (sp - 16#32).toNat ∨ (sp - 16#32).toNat + 4 ≤ 52996) :
    Steps P host ⟨initial sp, caller, [constI32 0, .plain (.call ⟨130⟩)]⟩
      ⟨(initial sp).setMem 0
        { memory with bytes := Memory.writeSlice memory.bytes (sp - 16#32).toNat diagnosticWord },
        caller, [constI32 0]⟩ := by
  have diagnostic : Memory.encodeLE 4 18995 = diagnosticWord := by kernel_rfl
  rw [← diagnostic]
  apply reactorNullDbCheck P host (address := 0) (logAddress := 1) (stack := 0) (memory := 0)
    (sp := sp) (fn := check) (logFn := logger) (type := checkType) (logType := loggerType) (mem := memory)
  · kernel_rfl
  · kernel_rfl
  · rfl
  · rfl
  · kernel_rfl
  · kernel_rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rw [show memory.bytes.size = 65536 from Array.size_replicate]
    exact fits
  · exact disjoint
  · exact fixtureZero

example (P : Profile) (host : HostSemantics Nat) :
    Steps P host ⟨initial 20, caller, [constI32 0, .plain (.call ⟨130⟩)]⟩
      ⟨(initial 20).setMem 0
        { memory with bytes := Memory.writeSlice memory.bytes 4 diagnosticWord }, caller, [constI32 0]⟩ :=
  fixture P host 20 (by decide) (Or.inr (by decide))

example (P : Profile) (host : HostSemantics Nat) :
    Steps P host ⟨initial 53016, caller, [constI32 0, .plain (.call ⟨130⟩)]⟩
      ⟨(initial 53016).setMem 0
        { memory with bytes := Memory.writeSlice memory.bytes 53000 diagnosticWord }, caller, [constI32 0]⟩ :=
  fixture P host 53016 (by decide) (Or.inl (by decide))

#print axioms originalNullDbCheck
#print axioms decodedNullDbCheckAndLogger
#print axioms originalDecode
#print axioms fixture
#print axioms reactorNullDbCheck

end SqliteWasm
