module

import SqliteWasm.OrdinaryVarintHelper
import SqliteWasm.VarintWitness

namespace SqliteWasm.OrdinaryVarint

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation (Expand)
open Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Exec
open SqliteWasm.ThreeByte (args postStore)
open SqliteWasm.ThreeByte.Symbolic (quotedHelper)
open SqliteWasm.VarintWitness (entry initial initialBytes memoryType put)
open SqliteWasmArtifact

set_option maxRecDepth 131072

private def caller : Frame := { module := { funcs := List.replicate 530 1 ++ [0] } }

private theorem fixtureBuffers (width : Nat) (bound : width ≤ 8) :
    Buffers initialBytes 16 128 width := by
  have size : initialBytes.size = 65536 := by kernel_rfl
  refine ⟨by decide +kernel, ?_, ?_, ?_, Or.inl ?_⟩
  · change 16 + width ≤ 4294967296
    omega
  · rw [size]
    change 16 + width ≤ 65536
    omega
  · rw [size]
    change 118 + width ≤ 65536
    omega
  · change 16 + width ≤ 118
    omega

private def reached (value : UInt64) (width : Nat) : Prop :=
  Steps (profile neverFail) Det.noHost
    ⟨initial, caller, vals (args 16 value) ++ [.plain (.call ⟨530⟩)]⟩
    ⟨postStore initial 0 ⟨memoryType, initialBytes⟩ 16 128 value, caller,
      [constI32 (BitVec.ofNat 32 width)]⟩

private theorem fixture (value : UInt64) (width : Nat) (enters : 3 ≤ width)
    (fits : Width value.toNat width) : reached value width :=
  putVarint_ordinary (putAddress := 0) (helperAddress := 1)
    (putInstance := entry put) (helperInstance := entry quotedHelper)
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) rfl rfl (Expand.iff.mpr rfl)
    (Expand.iff.mpr rfl) enters fits rfl rfl (fixtureBuffers width fits.ordinary)

-- The transition past three bytes, an input requiring both i64 halves, and the top ordinary value.
example : reached 2097152 4 ∧ reached 0x100000000 5 ∧ reached 0x00ffffffffffffff 8 := by
  refine ⟨fixture _ _ (by decide) ?_, fixture _ _ (by decide) ?_, fixture _ _ (by decide) ?_⟩
  all_goals exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

example : sourceFunction? original 547 = some quotedHelper := originalHelper

end SqliteWasm.OrdinaryVarint
