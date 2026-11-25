module

public import Silmaril.Wasm.Institution.Operational.Blocks.Context.Defs
public import Silmaril.Wasm.Execution.Core.Inversion.Defs
public import Silmaril.Wasm.SingleThreaded.Determinism.Head
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.Blocks.Context.Core
import Silmaril.Proofs.Wasm.Institution.Operational.Blocks.Context.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.Blocks.Context.V1
import Silmaril.Proofs.Wasm.Institution.Operational.Blocks.Context.Rules

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Blocks.Context

open Execution.Runtime (Value)

theorem return_typed_step {A : Type} {results : List NumType} {a b : Returning A}
    (typed : a.Typed results) (step : ReturnStep a b) : b.Typed results :=
  Proofs.typed_step typed step

theorem return_typed_run {A : Type} {results : List NumType} {a b : Returning A}
    (typed : a.Typed results) (run : ReturnRuns a b) : b.Typed results := by
  induction run with
  | refl => exact typed
  | tail _ step ih => exact return_typed_step ih step

section Core

open Execution.Core
open Wasm.Numerics (Profile)
open Wasm.SingleThreaded.Det (noHost)

variable {H : Type} {P : Profile} {s : Store H} {f : Frame} {dst : Config H}

/-- A step at the label preserves its surrounding operands and pending
instructions. A step inside it may update the current frame and store. -/
theorem core_label_iff {n : Nat} {saved : List Val} {body rest : List Admin} :
    Step P noHost ⟨s, f, vals saved ++ .label n [] body :: rest⟩ dst ↔
      (∃ mid, Step P noHost ⟨s, f, body⟩ mid ∧
        dst = ⟨mid.store, mid.frame, vals saved ++ .label n [] mid.code :: rest⟩) ∨
      ∃ out, LabelExit n [] body out ∧ dst = ⟨s, f, vals saved ++ out ++ rest⟩ :=
  Proofs.Core.label_iff

/-- A live entered function frame takes its step inside the block. The block
and function frame can have different arities. -/
theorem core_frame_iff {callee : Frame} {n k : Nat}
    {saved : List Val} {body rest : List Admin} :
    Step P noHost ⟨s, f, vals saved ++ .label n [] [.frame k callee body] :: rest⟩ dst ↔
      ∃ mid, Step P noHost ⟨s, f, [.frame k callee body]⟩ mid ∧
        dst = ⟨mid.store, mid.frame, vals saved ++ .label n [] mid.code :: rest⟩ :=
  Proofs.Core.frame_iff

theorem core_result_iff {scope : Scope Admin} {r : CallContinuation.Nested.Result} :
    let code := CallContinuation.Nested.resultCode coreValues .trap r
    Step P noHost ⟨s, f, scope.plug coreValues (fun n => .label n []) code⟩ dst ↔
      dst = ⟨s, f, coreValues scope.saved ++ code ++ scope.rest⟩ :=
  Proofs.Core.result_iff

theorem core_return_step_iff (a : Returning Admin) :
    Step P noHost ⟨s, f, coreCode a⟩ dst ↔
      ∃ b, ReturnStep a b ∧ dst = ⟨s, f, coreCode b⟩ :=
  Proofs.Core.return_step_iff a

theorem core_return_run_iff (a : Returning Admin) :
    Relation.ReflTransGen (Step P noHost) ⟨s, f, coreCode a⟩ dst ↔
      ∃ b, ReturnRuns a b ∧ dst = ⟨s, f, coreCode b⟩ :=
  Proofs.run_iff (fun q => (⟨s, f, coreCode q⟩ : Config H)) _ (fun {q _} => core_return_step_iff q)

end Core

section Lime1

open Wasm.Lime1.Execution
open Execution.Runtime (Frame)

variable {H : Type} {s : Store H} {f : Frame} {dst : Config H}

/-- A step at the label preserves its surrounding operands and pending
instructions. A step inside it may update the current frame and store. -/
theorem lime_label_iff {n : Nat} {saved : List Value} {body rest : List Admin} :
    Step CallFrame.limeNoHost ⟨s, f, values saved ++ .label n [] body :: rest⟩ dst ↔
      (∃ mid, Step CallFrame.limeNoHost ⟨s, f, body⟩ mid ∧
        dst = ⟨mid.store, mid.frame, values saved ++ .label n [] mid.code :: rest⟩) ∨
      ∃ out, PureStep f.module.types [.label n [] body] out ∧ dst = ⟨s, f, values saved ++ out ++ rest⟩ :=
  Proofs.Lime1.label_iff

/-- A live entered function frame takes its step inside the block. The block
and function frame can have different arities. -/
theorem lime_frame_iff {callee : Frame} {n k : Nat}
    {saved : List Value} {body rest : List Admin} :
    Step CallFrame.limeNoHost ⟨s, f, values saved ++ .label n [] [.frame k callee body] :: rest⟩ dst ↔
      ∃ mid, Step CallFrame.limeNoHost ⟨s, f, [.frame k callee body]⟩ mid ∧
        dst = ⟨mid.store, mid.frame, values saved ++ .label n [] mid.code :: rest⟩ :=
  Proofs.Lime1.frame_iff

theorem lime_result_iff {scope : Scope Admin} {r : CallContinuation.Nested.Result} :
    let code := CallContinuation.Nested.resultCode values .trap r
    Step CallFrame.limeNoHost ⟨s, f, scope.plug values (fun n => .label n []) code⟩ dst ↔
      dst = ⟨s, f, values scope.saved ++ code ++ scope.rest⟩ :=
  Proofs.Lime1.result_iff

theorem lime_return_step_iff (a : Returning Admin) :
    Step CallFrame.limeNoHost ⟨s, f, limeCode a⟩ dst ↔
      ∃ b, ReturnStep a b ∧ dst = ⟨s, f, limeCode b⟩ :=
  Proofs.Lime1.return_step_iff a

theorem lime_return_run_iff (a : Returning Admin) :
    Relation.ReflTransGen (Step CallFrame.limeNoHost) ⟨s, f, limeCode a⟩ dst ↔
      ∃ b, ReturnRuns a b ∧ dst = ⟨s, f, limeCode b⟩ :=
  Proofs.run_iff (fun q => (⟨s, f, limeCode q⟩ : Config H)) _ (fun {q _} => lime_return_step_iff q)

end Lime1

section V1

open Wasm.V1.Execution
open Execution.Runtime (Frame)

variable {H : Type} {s : Store H} {f : Frame} {dst : Config H}

/-- A step at the label preserves its surrounding operands and pending
instructions. A step inside it may update the current frame and store. -/
theorem v1_label_iff {n : Nat} {saved : List Value} {body rest : List Admin} :
    Step CallFrame.v1NoHost ⟨s, f, values saved ++ .label n [] body :: rest⟩ dst ↔
      (∃ mid, Step CallFrame.v1NoHost ⟨s, f, body⟩ mid ∧
        dst = ⟨mid.store, mid.frame, values saved ++ .label n [] mid.code :: rest⟩) ∨
      ∃ out, PureStep [.label n [] body] out ∧ dst = ⟨s, f, values saved ++ out ++ rest⟩ :=
  Proofs.V1.label_iff

/-- A live entered function frame takes its step inside the block. The block
and function frame can have different arities. -/
theorem v1_frame_iff {callee : Frame} {n k : Nat}
    {saved : List Value} {body rest : List Admin} :
    Step CallFrame.v1NoHost ⟨s, f, values saved ++ .label n [] [.frame k callee body] :: rest⟩ dst ↔
      ∃ mid, Step CallFrame.v1NoHost ⟨s, f, [.frame k callee body]⟩ mid ∧
        dst = ⟨mid.store, mid.frame, values saved ++ .label n [] mid.code :: rest⟩ :=
  Proofs.V1.frame_iff

theorem v1_result_iff {scope : Scope Admin} {r : CallContinuation.Nested.Result} :
    let code := CallContinuation.Nested.resultCode values .trap r
    Step CallFrame.v1NoHost ⟨s, f, scope.plug values (fun n => .label n []) code⟩ dst ↔
      dst = ⟨s, f, values scope.saved ++ code ++ scope.rest⟩ :=
  Proofs.V1.result_iff

theorem v1_return_step_iff (a : Returning Admin) :
    Step CallFrame.v1NoHost ⟨s, f, v1Code a⟩ dst ↔
      ∃ b, ReturnStep a b ∧ dst = ⟨s, f, v1Code b⟩ :=
  Proofs.V1.return_step_iff a

theorem v1_return_run_iff (a : Returning Admin) :
    Relation.ReflTransGen (Step CallFrame.v1NoHost) ⟨s, f, v1Code a⟩ dst ↔
      ∃ b, ReturnRuns a b ∧ dst = ⟨s, f, v1Code b⟩ :=
  Proofs.run_iff (fun q => (⟨s, f, v1Code q⟩ : Config H)) _ (fun {q _} => v1_return_step_iff q)

end V1

end Silmaril.Wasm.Institution.Operational.Blocks.Context
