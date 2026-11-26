module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Conditional.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Conditional.Readback

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Conditional

open Execution.Runtime (Frame Value)
open Wasm.Lime1.Execution

variable {H : Type} {base : Store H} {mem : Memory32 base} {host : HostSemantics H}
  {outer active : Frame} {results : List NumType} {a b : State H} {dst : Config H}

theorem Plan.start_code (plan : Plan H) (arity : Nat) (frame : Frame) (saved : List Value) (guard : BitVec 32) :
    (plan.start saved guard).renderCode arity frame =
      entered arity frame (values (saved ++ [i32 guard]) ++ expression plan.expr) := by
  cases plan <;> rfl

theorem Plan.start_ready {plan : Plan H} {saved : List Value} {guard : BitVec 32}
    (checked : plan.Checked base active.module (active.locals.map Value.type) results (saved.map Value.type))
    (contract : plan.Contract mem host) :
    Ready mem host active results (plan.start saved guard) :=
  Proofs.start_ready checked contract

/-- All edges retain the fixed-extent memory and checked stack or result.
The selected arm uses its own result signature until its native label exits. -/
theorem preserves (move : Edge mem host active a b)
    (ready : Ready mem host active results a.phase) (live : mem.Live a.bytes) :
    Ready mem host active results b.phase ∧ mem.Live b.bytes :=
  Proofs.preserves move ready live

/-- Exact native successors through the guard, block entry, selected arm,
and shared continuation. -/
theorem step_iff (ready : Ready mem host active results a.phase) (live : mem.Live a.bytes) :
    Step host (render mem outer active results.length a) dst ↔
      ∃ next, Edge mem host active a next ∧ dst = render mem outer active results.length next :=
  Proofs.step_iff ready live

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Conditional
