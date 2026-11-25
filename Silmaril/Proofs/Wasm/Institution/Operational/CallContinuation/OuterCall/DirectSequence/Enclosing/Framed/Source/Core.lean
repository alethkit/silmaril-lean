module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Code
public import Silmaril.Wasm.SingleThreaded.Determinism.Head
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Proofs.Core

open Execution.Core
open Execution.Runtime (Value)
open Wasm.Numerics (Profile)
open Wasm.SingleThreaded.Det (noHost)

private theorem enter_iff {H : Type} {P : Profile} {s : Store H} {caller : Execution.Runtime.Frame}
    {call : Invocation} {dst : Config H} (g : CoreGuard s caller call) :
    Step P noHost (coreConfig s caller call .invoke) dst ↔
      dst = coreConfig s caller call (.framed call.start) := by
  have enter := Computed.Sequence.wasm_entry_iff (P := P) (caller := caller) (dst := dst) g.allocated g.typed.args
  have init := Computed.Sequence.core_frame_forCall call.target.declaration.module call.args call.target.declaration.locals
  change Frame.forCall call.target.declaration.module.toCore (call.args.map Value.toCore)
    call.body.coreFunc.locals = call.context.frame.toCore at init
  rw [init, core_expression] at enter
  exact enter

theorem sound {H : Type} {P : Profile} {s : Store H} {caller : Execution.Runtime.Frame} {call : Invocation}
    {a b : State call} (g : CoreGuard s caller call) (edge : Edge call a b) :
    Step P noHost (coreConfig s caller call a) (coreConfig s caller call b) := by
  cases invert edge with
  | framed move => exact Framed.core_sound g.body move
  | ground rule =>
    cases rule with
    | resolve => exact (Computed.core_direct_call_iff g.resolves g.allocated).mpr rfl
    | enter => exact (enter_iff g).mpr rfl

theorem readback {H : Type} {P : Profile} {s : Store H} {caller : Execution.Runtime.Frame} {call : Invocation}
    {a : State call} {dst : Config H} (g : CoreGuard s caller call) (ready : Admitted a)
    (step : Step P noHost (coreConfig s caller call a) dst) :
    ∃ out, Edge call a out ∧ dst = coreConfig s caller call out := by
  cases a with
  | call => exact ⟨.invoke, fact .resolve, (Computed.core_direct_call_iff g.resolves g.allocated).mp step⟩
  | invoke => exact ⟨_, fact .enter, (enter_iff g).mp step⟩
  | framed phase =>
    obtain ⟨out, move, eq⟩ := (Framed.core_step_iff g.body ready).mp step
    exact ⟨.framed out, framed move, eq⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Proofs.Core
