module

import SqliteWasm.GetVarint
import Silmaril.Wasm.Execution.Core.Instantiation
import Silmaril.Wasm.Verify.Kernel.Defs

namespace SqliteWasm

open Silmaril.Formats.Sqlite
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (DefType Expand)
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

example (P : Profile) (host : HostSemantics Unit) :
    let before := memory 0x7f 0x21 0x22 0x23 0x24 0x25 0x26 0x27 0xa1
    let after := memory 0x7f 0 0 0 0 0 0 0 0xa1
    Steps P host
      ⟨initial before, caller, vals [.i32 2, .i32 2] ++ [.plain (.call ⟨434⟩)]⟩
      ⟨(initial before).setMem 1 after, caller, [constI32 1]⟩ := by
  let before := memory 0x7f 0x21 0x22 0x23 0x24 0x25 0x26 0x27 0xa1
  have read : Varint.read? (File.View.ofBytes ⟨before.bytes⟩) 2 =
      some (127, 3) := by
    dsimp only [before]
    kernel_rfl
  exact getVarint_of_read (s := initial before) (caller := caller) (fn := reader)
    (src := 2) (dst := 2) (instanceAddr := 0) (fi := callee) (memoryAddr := 1)
    (mem := before) (value := 127) (next := 3)
    rfl rfl rfl rfl (Expand.iff.mpr rfl) rfl read (by change 10 ≤ 12; decide)

example (P : Profile) (host : HostSemantics Unit) :
    let before := memory 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x7f 0xa2
    let after := memory 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0 0xa2
    Steps P host
      ⟨initial before, caller, vals [.i32 2, .i32 2] ++ [.plain (.call ⟨434⟩)]⟩
      ⟨(initial before).setMem 1 after, caller, [constI32 8]⟩ := by
  let before := memory 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x7f 0xa2
  have read : Varint.read? (File.View.ofBytes ⟨before.bytes⟩) 2 =
      some (72057594037927935, 10) := by
    dsimp only [before]
    kernel_rfl
  exact getVarint_of_read (s := initial before) (caller := caller) (fn := reader)
    (src := 2) (dst := 2) (instanceAddr := 0) (fi := callee) (memoryAddr := 1)
    (mem := before) (value := 72057594037927935) (next := 10)
    rfl rfl rfl rfl (Expand.iff.mpr rfl) rfl read (by change 10 ≤ 12; decide)

example (P : Profile) (host : HostSemantics Unit) :
    let before := memory 0x80 0x80 0x80 0x80 0x80 0x80 0x80 0x80 0x80
    let after := memory 0x80 0 0 0 0 0 0 0 0x80
    Steps P host
      ⟨initial before, caller, vals [.i32 2, .i32 2] ++ [.plain (.call ⟨434⟩)]⟩
      ⟨(initial before).setMem 1 after, caller, [constI32 9]⟩ := by
  let before := memory 0x80 0x80 0x80 0x80 0x80 0x80 0x80 0x80 0x80
  have read : Varint.read? (File.View.ofBytes ⟨before.bytes⟩) 2 =
      some (128, 11) := by
    dsimp only [before]
    kernel_rfl
  exact getVarint_of_read (s := initial before) (caller := caller) (fn := reader)
    (src := 2) (dst := 2) (instanceAddr := 0) (fi := callee) (memoryAddr := 1)
    (mem := before) (value := 128) (next := 11)
    rfl rfl rfl rfl (Expand.iff.mpr rfl) rfl read (by change 10 ≤ 12; decide)

end SqliteWasm
