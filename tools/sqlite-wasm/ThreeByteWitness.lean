module

public import SqliteWasm.ThreeByteContract
public import SqliteWasm.VarintWitness
import Silmaril.Wasm.Execution.Core.Soundness
import Silmaril.Wasm.Execution.Core.Soundness.StateFacts

@[expose] public section

namespace SqliteWasm.ThreeByte

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Exec Silmaril.Wasm.Verify.Kernel
open SqliteWasm.VarintWitness (entry initial initialBytes initialTyped memoryType moduleInst put putLong
  signature threeByteValue)

set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

private theorem enteredTyped (value : UInt64) {slot : Nat} {fn : Func}
    (found : initial.funcs[slot]? = some (entry fn)) :
    ∃ C it, AdminOk initial C (activation moduleInst fn 16 value) it := by
  have sig : Expand signature (.func (.cons Ty.i32 (.cons Ty.i64 .nil)) (.cons Ty.i32 .nil)) :=
    Expand.iff.mpr rfl
  have canInvoke : InvokeOk initial slot (args 16 value) :=
    ⟨entry fn, _, _, found, sig, .cons (.num _) (.cons (.num _) .nil)⟩
  obtain ⟨_, _, _, _, _, typed⟩ := invoke_ok initialTyped canInvoke
  have enter : Step (profile neverFail) Det.noHost (invoke initial slot (args 16 value))
      ⟨initial, {}, [activation moduleInst fn 16 value]⟩ := by
    have call := Step.callRefFunc (P := profile neverFail) (host := Det.noHost) (f := {})
      (c := .callRefType signature) (vs := args 16 value) trivial found sig rfl rfl
    unfold invoke
    rw [found]
    exact call
  obtain ⟨C, ⟨_, frameOk⟩, admins⟩ :=
    (Step.preservation divHost_ok typed (Step.of_noHost divHost enter)).1
  have noTypes : C.toTypeCtx.types = [] :=
    FrameOk.types_eq (show FrameOk initial {} C from frameOk)
  have contextOk : C.toTypeCtx.Ok := by
    intro d member
    simp [noTypes] at member
  obtain ⟨_, it, box, _⟩ := AdminsOk.single_inv contextOk admins
  exact ⟨C, it, box⟩

private def fixture (value : UInt64) : Config Unit :=
  ⟨initial, callFrame moduleInst put 16 value, [activation moduleInst putLong 16 value]⟩

private theorem fixtureTyped (value : UInt64) : ∃ ts, ConfigOk (fixture value) ts := by
  obtain ⟨_, _, wrapper⟩ := enteredTyped value (slot := 0) (fn := put) rfl
  obtain ⟨_, _, callerContext, callerTyped, _, _, _⟩ := AdminOk.frame_invCtl wrapper
  obtain ⟨_, it, helper⟩ := enteredTyped value (slot := 1) (fn := putLong) rfl
  obtain ⟨_, _, _, helperFrame, arity, body, results⟩ := AdminOk.frame_invCtl helper
  exact ⟨it.results, callerContext, ⟨initialTyped, callerTyped⟩,
    AdminsOk.single' (AdminOk.frame helperFrame arity body results)
      (fun t ht => TyOk.of_empty _ (results t ht))⟩

private def final (value : UInt64) : Config Unit :=
  ⟨postStore initial 0 ⟨memoryType, initialBytes⟩ 16 128 value,
    callFrame moduleInst put 16 value, [constI32 3]⟩

private theorem fromRun {value : UInt64}
    (ran : runIK neverFail 300 (fixture value) = (final value, true)) :
    HelperRun (profile neverFail) Det.noHost initial (callFrame moduleInst put 16 value)
      putLong moduleInst 16 128 value 0 ⟨memoryType, initialBytes⟩ := by
  refine ⟨by kernel_rfl, ?_⟩
  obtain ⟨_, typed⟩ := fixtureTyped value
  rw [runIK_eq] at ran
  have steps := runI_steps_typed (o := neverFail) 300 typed
  rw [ran] at steps
  exact steps

/-- The isolated quoted helper writes both expected byte ranges at the lower and upper
ends of the three-byte interval, in the typed one-page fixture. -/
theorem helperEdges :
    HelperRun (profile neverFail) Det.noHost initial (callFrame moduleInst put 16 threeByteValue)
      putLong moduleInst 16 128 threeByteValue 0 ⟨memoryType, initialBytes⟩ ∧
    HelperRun (profile neverFail) Det.noHost initial (callFrame moduleInst put 16 2097151)
      putLong moduleInst 16 128 2097151 0 ⟨memoryType, initialBytes⟩ :=
  ⟨fromRun (by kernel_rfl), fromRun (by kernel_rfl)⟩

private theorem wrapperOfHelper (value : UInt64) (lower : 16384 ≤ value.toNat)
    (caller : Frame) (bound : initial.func? caller ⟨530⟩ = some (0, entry put))
    (helper : HelperRun (profile neverFail) Det.noHost initial (callFrame moduleInst put 16 value)
      putLong moduleInst 16 128 value 0 ⟨memoryType, initialBytes⟩) :
    Steps (profile neverFail) Det.noHost
      ⟨initial, caller, vals (args 16 value) ++ [.plain (.call ⟨530⟩)]⟩
      ⟨postStore initial 0 ⟨memoryType, initialBytes⟩ 16 128 value, caller, [constI32 3]⟩ :=
  putVarint_threeByte_of_helper (helperAddress := 1) (helperInstance := entry putLong)
    (by kernel_rfl) bound (by kernel_rfl) rfl rfl
    (Expand.iff.mpr rfl) (Expand.iff.mpr rfl) lower helper

/-- With the quoted wrapper linked at slot 530, compose each endpoint's isolated helper
execution with the caller proof. -/
theorem wrapperEdges (caller : Frame) (bound : initial.func? caller ⟨530⟩ = some (0, entry put)) :
    ∀ value : UInt64, value = threeByteValue ∨ value = 2097151 →
      Steps (profile neverFail) Det.noHost
        ⟨initial, caller, vals (args 16 value) ++ [.plain (.call ⟨530⟩)]⟩
        ⟨postStore initial 0 ⟨memoryType, initialBytes⟩ 16 128 value, caller, [constI32 3]⟩ := by
  rintro _ (rfl | rfl)
  · exact wrapperOfHelper _ (by decide +kernel) caller bound helperEdges.1
  · exact wrapperOfHelper _ (by decide +kernel) caller bound helperEdges.2

#print axioms helperEdges
#print axioms wrapperEdges

end SqliteWasm.ThreeByte
