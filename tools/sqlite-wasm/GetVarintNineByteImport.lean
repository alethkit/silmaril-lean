module

import SqliteWasm.GetVarintOneByte
import SqliteWasm.GetVarintTwoByte
import SqliteWasm.GetVarintThreeByte
import SqliteWasm.GetVarintFourByte
import SqliteWasm.GetVarintFiveByte
import SqliteWasm.GetVarintSixByte
import SqliteWasm.GetVarintSevenByte
import SqliteWasm.GetVarintEightByte
import SqliteWasm.GetVarintNineByte
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

private def memory (a b c d e f g h i : UInt8) : MemInst :=
  ⟨⟨.i32, ⟨0, none⟩⟩, ⟨#[0x5a, 0x5b, a, b, c, d, e, f, g, h, i, 0xa5]⟩⟩

private def initial (mem : MemInst) : Store Unit :=
  { funcs := [callee], mems := [memory 0 0 0 0 0 0 0 0 0, mem] }

example : sourceFunction? original 434 = some reader :=
  originalGetVarintFunction.trans rfl

example (P : Profile) (host : HostSemantics Unit) :
    let before := memory 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff
    Varint.read? (File.View.ofBytes ⟨before.bytes⟩) 2 = some (18446744073709551615, 11) ∧
    Steps P host
      ⟨initial before, caller, vals [.i32 2, .i32 2] ++ [.plain (.call ⟨434⟩)]⟩
      ⟨(initial before).setMem 1 before, caller, [constI32 9]⟩ := by
  let before := memory 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff
  exact getVarint_nineByte (s := initial before) (caller := caller) (src := 2) (dst := 2)
    (instanceAddr := 0) (fi := callee) (fn := reader)
    (first := 0xff) (second := 0xff) (third := 0xff) (fourth := 0xff) (fifth := 0xff)
    (sixth := 0xff) (seventh := 0xff) (eighth := 0xff) (ninth := 0xff)
    (memoryAddr := 1) (mem := before)
    rfl rfl rfl rfl (Expand.iff.mpr rfl) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by change 10 ≤ 12; decide)

private def replay (before after : MemInst) : Prop :=
  runIK neverFail 192
    ⟨initial before, caller, vals [.i32 2, .i32 2] ++ [.plain (.call ⟨434⟩)]⟩ =
      (⟨(initial before).setMem 1 after, caller, [constI32 9]⟩, true)

example : replay (memory 0x80 0x80 0x80 0x80 0x80 0x80 0x80 0x80 0)
    (memory 0 0 0 0 0 0 0 0 0) := by
  unfold replay
  kernel_rfl

example : replay (memory 0x80 0xc0 0x80 0x80 0x80 0x80 0x80 0x80 0)
    (memory 0 0 0 0 0 0 0 1 0) := by
  unfold replay
  kernel_rfl

example : replay (memory 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)
    (memory 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff) := by
  unfold replay
  kernel_rfl

example : Varint.read? (File.View.ofBytes ⟨(memory 0x80 0xc0 0x80 0x80 0x80 0x80 0x80 0x80 0).bytes⟩) 2 =
    some (72057594037927936, 11) := by
  kernel_rfl

example : Varint.read? (File.View.ofBytes ⟨(memory 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff).bytes⟩) 2 =
    some (18446744073709551615, 11) := by
  kernel_rfl

end SqliteWasm
