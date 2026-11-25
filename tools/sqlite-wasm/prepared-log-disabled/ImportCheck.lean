module

import SqliteWasm.PreparedLogDisabled
import SqliteWasm.ArtifactCheck
import Silmaril.Wasm.Verify.Kernel.Defs

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (DefType)
open SqliteWasmArtifact

set_option maxRecDepth 65536

sqlite_check_eq originalLogger : sourceFunction? original 26 = definedFunction? sqlite 26

theorem decodedLogger :
    (Binary.Core.decode? originalBytes.toByteArray).bind (fun m => definedFunction? m 26) =
      definedFunction? sqlite 26 := by
  rw [originalDecode, Option.bind_some]

example (P : Profile) (host : HostSemantics Nat) (err fmt fmtArgs : BitVec 32) :
    ∃ runtime frame address memory mem,
      ((Binary.Core.decode? originalBytes.toByteArray).bind
        (fun decoded => prepareDirect? evalConst? reactorTypedImports decoded reactorImportAddrs)) =
          some (runtime, frame, none) ∧
      frame.module.funcs[26]? = some address ∧ runtime.mem? frame ⟨0⟩ = some (memory, mem) ∧
      (Memory.load mem.bytes 52996 4 = some 0 →
        Steps P host ⟨runtime, frame,
          vals [.i32 err, .i32 fmt, .i32 fmtArgs] ++ [.plain (.call ⟨26⟩)]⟩ ⟨runtime, frame, []⟩) := by
  rw [originalDecode, Option.bind_some]
  exact reactorPreparedLogDisabled P host err fmt fmtArgs

private def fn : Func := (definedFunction? sqlite 26).get (by kernel_rfl)
private def fnType : DefType := ((allocTypes sqlite.types)[fn.type.toNat]?).get (by kernel_rfl)
private def linked : ModuleInst := { funcs := List.replicate 27 0, globals := [0], mems := [0] }
private def caller : Frame := { module := linked, locals := [some (.i32 17), some (.i64 23)] }
private def mappedMemory : MemInst :=
  ⟨⟨.i32, ⟨1, none⟩⟩, ⟨Array.replicate 65536 0⟩⟩
private def initial : Store Nat :=
  { funcs := [⟨fnType, linked, .wasm fn⟩]
    mems := [mappedMemory, ⟨⟨.i32, ⟨1, none⟩⟩, ⟨((Array.replicate 65534 0).push 0xa5).push 0x5a⟩⟩]
    globals := [⟨⟨.var, .i32⟩, .i32 256⟩, ⟨⟨.var, .i32⟩, .i32 43⟩] }

private theorem fixtureZero : Memory.load mappedMemory.bytes 52996 4 = some 0 := by
  have size : mappedMemory.bytes.size = 65536 :=
    Array.size_replicate
  have read : mappedMemory.bytes.extract 52996 53000 = ⟨Array.replicate 4 0⟩ := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    change (Array.replicate 65536 (0 : UInt8)).extract 52996 53000 = Array.replicate 4 0
    rw [Array.extract_replicate]
    rfl
  unfold Memory.load Memory.readBytes
  rw [size, ite_eq_left (by decide : 52996 + 4 ≤ 65536), read]
  rfl

example (P : Profile) (host : HostSemantics Nat) :
    Steps P host ⟨initial, caller, vals [.i32 21, .i32 17, .i32 23] ++ [.plain (.call ⟨26⟩)]⟩
      ⟨initial, caller, []⟩ := by
  apply reactorLogDisabledCall P host (address := 0) (stack := 0) (ma := 0) (mem := mappedMemory)
    (sp := 256) (fn := fn) (type := fnType) 21 17 23
  · kernel_rfl
  · kernel_rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact fixtureZero

#print axioms originalLogger
#print axioms decodedLogger
#print axioms fixtureZero
#print axioms originalDecode
#print axioms reactorLogDisabledCall
#print axioms reactorPreparedLogDisabled

end SqliteWasm
