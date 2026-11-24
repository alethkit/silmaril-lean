module

import SqliteWasm.PutVarint
import SqliteWasm.VarintWitness

namespace SqliteWasm.PutVarint

open Silmaril.Formats.Sqlite
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation (Expand)
open Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Exec
open ThreeByte (args)
open ThreeByte.Symbolic (quotedHelper)
open VarintWitness (entry initial initialBytes memoryType moduleInst put stackPointer)

set_option maxRecDepth 131072

private def caller : Frame := { module := { funcs := List.replicate 530 1 ++ [0] } }
private def mem : MemInst := ⟨memoryType, initialBytes⟩

-- Use different memory addresses for the wrapper and the helper.
private def wrapper : FuncInst Unit :=
  { entry put with module := { moduleInst with mems := [1], globals := [] } }

private def shortStore : Store Unit :=
  { initial with funcs := [wrapper], mems := [mem, mem], globals := [] }

private def longStore (sp : BitVec 32) : Store Unit :=
  { shortStore with
    funcs := [wrapper, entry quotedHelper]
    globals := [⟨stackPointer.type, .i32 sp⟩] }

private def reached (s : Store Unit) (value : UInt64) (address : Nat) (sp : BitVec 32) : Prop :=
  Steps (profile neverFail) Det.noHost
    ⟨s, caller, vals (args 0 value) ++ [.plain (.call ⟨530⟩)]⟩
    ⟨s.setMem address { mem with bytes := outputBytes initialBytes 0 sp value }, caller,
      [constI32 (BitVec.ofNat 32 (Varint.encode value).length)]⟩

private theorem call (s : Store Unit) (value : UInt64) (address : Nat) (sp : BitVec 32)
    (bound : s.funcs[0]? = some wrapper)
    (premises : MemoryPremises s put wrapper 0 sp value address mem) :
    reached s value address sp :=
  SqliteWasm.putVarint (by kernel_rfl) (by kernel_rfl) bound rfl (Expand.iff.mpr rfl) premises

-- The inline paths work with no loaded helper and no global.
example : reached shortStore 127 1 0 ∧ reached shortStore 128 1 0 := by
  refine ⟨call _ _ _ _ rfl ?_, call _ _ _ _ rfl ?_⟩
  all_goals exact ⟨rfl, by decide +kernel⟩

example : reached (longStore 128) 16384 0 128 := by
  apply call _ _ _ _ rfl
  refine ⟨1, entry quotedHelper, 0, stackPointer.type, ?_, rfl, Expand.iff.mpr rfl, rfl, rfl, ?_⟩
  · kernel_rfl
  · exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      Or.inl (by decide +kernel)⟩

-- The widest branch reads global 0 even with a zero stack pointer and writes no scratch.
example : reached (longStore 0) 0x0100000000000000 0 0 ∧
    reached (longStore 0) 0xffffffffffffffff 0 0 := by
  refine ⟨call _ _ _ _ rfl ?_, call _ _ _ _ rfl ?_⟩
  all_goals
    refine ⟨1, entry quotedHelper, 0, stackPointer.type, ?_, rfl, Expand.iff.mpr rfl, rfl, rfl, ?_⟩
    · kernel_rfl
    · exact ⟨by decide +kernel, by decide +kernel⟩

example : (Varint.encode 0x0100000000000000).toList =
    [0x80, 0xc0, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0] := by kernel_rfl

example : (Varint.encode 0xffffffffffffffff).toList = List.replicate 9 0xff := by kernel_rfl

end SqliteWasm.PutVarint
