module

import SqliteWasm.ThreeByteHelper
import SqliteWasm.VarintWitness

namespace SqliteWasm.ThreeByte

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation (Expand)
open Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Exec
open SqliteWasm.ThreeByte.Symbolic
open SqliteWasm.VarintWitness (entry initial initialBytes memoryType put)

set_option maxRecDepth 131072

private def caller : Frame := { module := { funcs := List.replicate 530 1 ++ [0] } }

private theorem fixtureBuffers : Buffers initialBytes 16 128 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    Or.inl (by decide +kernel)⟩

example (value : UInt64) (lower : 16384 ≤ value.toNat) (upper : value.toNat < 2097152) :
    Steps (profile neverFail) Det.noHost
      ⟨initial, caller, vals (args 16 value) ++ [.plain (.call ⟨530⟩)]⟩
      ⟨postStore initial 0 ⟨memoryType, initialBytes⟩ 16 128 value, caller, [constI32 3]⟩ :=
  putVarint_threeByte (putAddress := 0) (helperAddress := 1)
    (putInstance := entry put) (helperInstance := entry quotedHelper)
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) rfl rfl (Expand.iff.mpr rfl)
    (Expand.iff.mpr rfl) lower upper rfl rfl fixtureBuffers

end SqliteWasm.ThreeByte
