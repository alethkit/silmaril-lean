module

import SqliteWasm.GetVarintOneByte
import Silmaril.Wasm.Execution.Core.Instantiation

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
  { module := { funcs := List.replicate 434 0 ++ [0], mems := [0] }
    locals := [some (.i32 42)] }

private def input : MemInst :=
  ⟨⟨.i32, ⟨0, none⟩⟩, ⟨#[0x5a, 0x5b, 0xfe, 0xff, 127, 9, 9, 9, 9, 9, 0xa5]⟩⟩

private def output : MemInst :=
  { input with bytes := ⟨#[0x5a, 0x5b, 127, 0, 0, 0, 0, 0, 0, 0, 0xa5]⟩ }

private def initial : Store Unit := { funcs := [callee], mems := [input, input] }

example : sourceFunction? original 434 = some reader :=
  originalGetVarintFunction.trans rfl

-- The write at [2, 10) overwrites the original input at offset 4.
example (P : Profile) (host : HostSemantics Unit) :
    Varint.read? (File.View.ofBytes ⟨input.bytes⟩) 4 = some (127, 5) ∧
    Steps P host ⟨initial, caller, vals [.i32 4, .i32 2] ++ [.plain (.call ⟨434⟩)]⟩
      ⟨initial.setMem 1 output, caller, [constI32 1]⟩ :=
  getVarint_oneByte (P := P) (host := host) (s := initial) (caller := caller) (fn := reader)
    (instanceAddr := 0) (fi := callee) (src := 4) (dst := 2) (byte := 127)
    (memoryAddr := 1) (mem := input)
    rfl rfl rfl rfl (Expand.iff.mpr rfl)
    rfl rfl (by decide +kernel) (by decide +kernel)

end SqliteWasm
