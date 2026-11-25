module

import SqliteWasm.PreparedVarintOrdinaryRoundtrip
import Silmaril.Wasm.Verify.Kernel.Defs

namespace SqliteWasm

open Silmaril.Formats.Sqlite
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Validation (DefType)
open Silmaril.Wasm.Verify.Kernel
open SqliteWasmArtifact

set_option maxRecDepth 131072
set_option maxHeartbeats 1500000

example (P : Profile) (host : HostSemantics Nat) :
    ∃ runtime frame mem address,
      ((Binary.Core.decode? originalBytes.toByteArray).bind
        (fun decoded => prepareDirect? evalConst? reactorTypedImports decoded reactorImportAddrs)) =
          some (runtime, frame, none) ∧
      runtime.mem? frame ⟨0⟩ = some (address, mem) ∧
      ∀ (ptr : BitVec 32) (value : UInt64) (width : Nat),
        (ptr = 126098 ∧ value = 16384 ∧ width = 3) ∨
          (ptr = 131064 ∧ value = 0x00ffffffffffffff ∧ width = 8) →
        let scratch := Memory.writeSlice mem.bytes 126102 ⟨⟨(Varint.encode value).toList.reverse⟩⟩
        let written := Memory.writeSlice scratch ptr.toNat (Varint.encode value).data
        let final := Memory.writeSlice written ptr.toNat (Memory.encodeLE 8 value.toNat)
        Varint.read? (File.View.ofBytes ⟨written⟩) ptr.toNat = some (value, ptr.toNat + width) ∧
        Steps P host
          ⟨runtime, frame, vals [.i32 ptr, .i64 value.toBitVec] ++ [.plain (.call ⟨530⟩)] ++
            vals [.i32 ptr, .i32 ptr] ++ [.plain (.call ⟨434⟩)]⟩
          ⟨runtime.setMem address { mem with bytes := final }, frame,
            vals [.i32 (BitVec.ofNat 32 width), .i32 (BitVec.ofNat 32 width)]⟩ := by
  rw [originalDecode, Option.bind_some]
  obtain ⟨runtime, frame, mem, address, prep, mapped, size, roundtrip⟩ :=
    reactorPreparedOrdinaryRoundtrip P host
  refine ⟨runtime, frame, mem, address, prep, mapped, ?_⟩
  intro ptr value width fixture
  rcases fixture with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact roundtrip 126098 16384 3 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by rw [size]; decide +kernel) (by decide +kernel)
  · exact roundtrip 131064 0x00ffffffffffffff 8 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by rw [size]; decide +kernel) (by decide +kernel)

private def writer : Func := (definedFunction? sqlite 530).get (by kernel_rfl)
private def reader : Func := (definedFunction? sqlite 434).get (by kernel_rfl)
private def helper : Func := (definedFunction? sqlite 547).get (by kernel_rfl)
private def typeFor (fn : Func) : Option DefType := (allocTypes sqlite.types)[fn.type.toNat]?

private def caller : Frame :=
  { module :=
      { funcs := (List.replicate 434 0) ++ [1] ++ (List.replicate 112 0) ++ [2]
        mems := [0]
        globals := [0] }
    locals := [some (.i32 42)] }

private def memory : MemInst :=
  ⟨⟨.i32, ⟨0, none⟩⟩, ⟨#[0xa5] ++ Array.replicate 30 0xee ++ #[0x5a]⟩⟩

private def initial : Store Nat :=
  { funcs := [⟨(typeFor writer).get (by kernel_rfl), caller.module, .wasm writer⟩,
              ⟨(typeFor reader).get (by kernel_rfl), caller.module, .wasm reader⟩,
              ⟨(typeFor helper).get (by kernel_rfl), caller.module, .wasm helper⟩]
    mems := [memory]
    globals := [⟨⟨.var, .i32⟩, .i32 32⟩] }

private def replay (ptr : BitVec 32) (value : BitVec 64) (width : BitVec 32)
    (expected : ByteArray) : Prop :=
  runIK neverFail 1024
    ⟨initial, caller, vals [.i32 ptr, .i64 value] ++ [.plain (.call ⟨530⟩)] ++
      vals [.i32 ptr, .i32 ptr] ++ [.plain (.call ⟨434⟩)]⟩ =
    (⟨initial.setMem 0 { memory with bytes := expected }, caller, vals [.i32 width, .i32 width]⟩, true)

-- The writer leaves reverse digits at scratch address 22, next to its disjoint output.
example :
    runIK neverFail 1024
      ⟨initial, caller, vals [.i32 19, .i64 16384] ++ [.plain (.call ⟨530⟩)]⟩ =
      (⟨initial.setMem 0
          { memory with bytes := Memory.writeSlice memory.bytes 19 ⟨#[0x81, 0x80, 0, 0, 0x80, 0x81]⟩ },
        caller, [constI32 3]⟩, true) := by
  kernel_rfl

-- The reader's wider output overwrites all three scratch bytes.
example : replay 19 16384 3
    (Memory.writeSlice memory.bytes 19 ⟨#[0, 0x40, 0, 0, 0, 0, 0, 0]⟩) := by
  unfold replay
  kernel_rfl

-- With a disjoint readback, all eight reversed scratch octets remain.
example : replay 1 0x00ffffffffffffff 8
    (Memory.writeSlice
      (Memory.writeSlice memory.bytes 22 ⟨#[0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]⟩)
      1 ⟨#[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0]⟩) := by
  unfold replay
  kernel_rfl

#print axioms originalDecode
#print axioms originalPutVarintFunction
#print axioms originalGetVarintFunction
#print axioms originalPutVarintLongFunction
#print axioms reactorPreparedOrdinaryRoundtrip

end SqliteWasm
