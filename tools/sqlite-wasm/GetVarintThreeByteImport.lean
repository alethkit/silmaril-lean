module

import SqliteWasm.GetVarintOneByte
import SqliteWasm.GetVarintThreeByte
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
  { module := { funcs := List.replicate 435 0, mems := [0] }
    locals := [some (.i32 42)] }

private def input (first second third : UInt8) : MemInst :=
  ⟨⟨.i32, ⟨0, none⟩⟩, ⟨#[0x5a, 0x5b, 9, 9, first, second, third, 9, 9, 9, 0xa5]⟩⟩

private def output (lo mid hi : UInt8) : MemInst :=
  { input 0 0 0 with bytes := ⟨#[0x5a, 0x5b, lo, mid, hi, 0, 0, 0, 0, 0, 0xa5]⟩ }

private def initial (first second third : UInt8) : Store Unit :=
  { funcs := [callee], mems := [input 0 0 0, input first second third] }

example : sourceFunction? original 434 = some reader :=
  originalGetVarintFunction.trans rfl

private theorem check (P : Profile) (host : HostSemantics Unit) (first second third : UInt8)
    (continues : 128 ≤ first.toNat) (continuesAgain : 128 ≤ second.toNat)
    (ends : third.toNat < 128) :
    let value := (first.toNat % 128 * 128 + second.toNat % 128) * 128 + third.toNat
    let bytes := Memory.writeSlice (input first second third).bytes 2 (Memory.encodeLE 8 value)
    Varint.read? (File.View.ofBytes ⟨(input first second third).bytes⟩) 4 =
        some (UInt64.ofNat value, 7) ∧
    Steps P host
      ⟨initial first second third, caller, vals [.i32 4, .i32 2] ++ [.plain (.call ⟨434⟩)]⟩
      ⟨(initial first second third).setMem 1
        { input first second third with bytes := bytes }, caller, [constI32 3]⟩ := by
  exact getVarint_threeByte (s := initial first second third) (caller := caller) (fn := reader)
    (instanceAddr := 0) (fi := callee) (src := 4) (dst := 2) (first := first) (second := second) (third := third)
    (memoryAddr := 1) (mem := input first second third)
    rfl rfl rfl rfl (Expand.iff.mpr rfl) rfl rfl rfl rfl continues continuesAgain ends (by change 10 ≤ 11; decide)

example (P : Profile) (host : HostSemantics Unit) :
    Steps P host ⟨initial 0x80 0x80 0, caller, vals [.i32 4, .i32 2] ++ [.plain (.call ⟨434⟩)]⟩
      ⟨(initial 0x80 0x80 0).setMem 1 (output 0 0 0), caller, [constI32 3]⟩ :=
  (check P host 0x80 0x80 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)).2

example (P : Profile) (host : HostSemantics Unit) :
    Steps P host ⟨initial 0x81 0x80 0, caller, vals [.i32 4, .i32 2] ++ [.plain (.call ⟨434⟩)]⟩
      ⟨(initial 0x81 0x80 0).setMem 1 (output 0 0x40 0), caller, [constI32 3]⟩ :=
  (check P host 0x81 0x80 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)).2

example (P : Profile) (host : HostSemantics Unit) :
    Steps P host ⟨initial 0xff 0xff 0x7f, caller, vals [.i32 4, .i32 2] ++ [.plain (.call ⟨434⟩)]⟩
      ⟨(initial 0xff 0xff 0x7f).setMem 1 (output 0xff 0xff 0x1f), caller, [constI32 3]⟩ :=
  (check P host 0xff 0xff 0x7f (by decide +kernel) (by decide +kernel) (by decide +kernel)).2

end SqliteWasm
