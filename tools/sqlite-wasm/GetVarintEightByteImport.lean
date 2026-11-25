module

import SqliteWasm.GetVarintOneByte
import SqliteWasm.GetVarintTwoByte
import SqliteWasm.GetVarintThreeByte
import SqliteWasm.GetVarintFourByte
import SqliteWasm.GetVarintFiveByte
import SqliteWasm.GetVarintSixByte
import SqliteWasm.GetVarintSevenByte
import SqliteWasm.GetVarintEightByte
import Silmaril.Wasm.Verify.Kernel.Defs
import Silmaril.Wasm.Execution.Core.Instantiation

namespace SqliteWasm

open Silmaril.Formats.Sqlite
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (DefType Expand)
open Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Verify.Kernel
open SqliteWasmArtifact

set_option maxRecDepth 65536

private def reader : Func := (definedFunction? sqlite 434).get rfl

private def runtimeType : DefType :=
  let group := (sqlite.types[reader.type.toNat]?).get rfl
  ((allocTypes [group])[0]?).get rfl

private def callee : FuncInst Unit := ⟨runtimeType, { mems := [1] }, .wasm reader⟩

private def caller : Frame :=
  { module := { funcs := List.replicate 435 0, mems := [0] }
    locals := [some (.i32 42)] }

private def input (first second third fourth fifth sixth seventh eighth : UInt8) : MemInst :=
  ⟨⟨.i32, ⟨0, none⟩⟩, ⟨#[0x5a, 0x5b, first, second, third, fourth, fifth, sixth, seventh, eighth, 0xa5]⟩⟩

private def output (d0 d1 d2 d3 d4 d5 d6 : UInt8) : MemInst :=
  { input 0 0 0 0 0 0 0 0 with bytes := ⟨#[0x5a, 0x5b, d0, d1, d2, d3, d4, d5, d6, 0, 0xa5]⟩ }

private def initial (first second third fourth fifth sixth seventh eighth : UInt8) : Store Unit :=
  { funcs := [callee], mems := [input 0 0 0 0 0 0 0 0, input first second third fourth fifth sixth seventh eighth] }

example : sourceFunction? original 434 = some reader :=
  originalGetVarintFunction.trans rfl

-- Apply the theorem through an ordinary import at the upper canonical endpoint.
example (P : Profile) (host : HostSemantics Unit) :
    Varint.read? (File.View.ofBytes ⟨(input 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x7f).bytes⟩) 2 =
      some (72057594037927935, 10) ∧
    Steps P host
      ⟨initial 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x7f, caller,
        vals [.i32 2, .i32 2] ++ [.plain (.call ⟨434⟩)]⟩
      ⟨(initial 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x7f).setMem 1 (output 0xff 0xff 0xff 0xff 0xff 0xff 0xff),
        caller, [constI32 8]⟩ := by
  exact getVarint_eightByte (s := initial 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x7f)
    (caller := caller) (src := 2) (dst := 2) (instanceAddr := 0) (fi := callee) (fn := reader)
    (first := 0xff) (second := 0xff) (third := 0xff) (fourth := 0xff) (fifth := 0xff)
    (sixth := 0xff) (seventh := 0xff) (eighth := 0x7f)
    (memoryAddr := 1) (mem := input 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x7f)
    rfl rfl rfl rfl (Expand.iff.mpr rfl) rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by change 10 ≤ 11; decide)

-- Each replay uses the same eight-byte span for the source and destination.
private def replay (start : Store Unit) (result : MemInst) : Prop :=
  runIK neverFail 176
    ⟨start, caller, vals [.i32 2, .i32 2] ++ [.plain (.call ⟨434⟩)]⟩ =
      (⟨start.setMem 1 result, caller, [constI32 8]⟩, true)

example : replay (initial 0x80 0x80 0x80 0x80 0x80 0x80 0x80 0) (output 0 0 0 0 0 0 0) := by
  unfold replay
  kernel_rfl

example : replay (initial 0x81 0x80 0x80 0x80 0x80 0x80 0x80 0) (output 0 0 0 0 0 0 2) := by
  unfold replay
  kernel_rfl

example : replay (initial 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x7f) (output 0xff 0xff 0xff 0xff 0xff 0xff 0xff) := by
  unfold replay
  kernel_rfl

end SqliteWasm
