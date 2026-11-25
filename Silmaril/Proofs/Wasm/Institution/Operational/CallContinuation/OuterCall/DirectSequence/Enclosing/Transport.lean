module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Native.Defs
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Proofs

open Execution
open StraightLine
open Computed (v1Syntax limeSyntax coreSyntax)

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (ctx : Context) (site : Site) (q : State ctx site) :
    (v1Config s ctx site q).toLime = limeConfig (s.mapCode Wasm.V1.Func.toLime) ctx site q := by
  open Wasm.V1.Execution in
  cases q with
  | active phase =>
    have body : codeToLime (DirectSequence.v1Code site phase) = DirectSequence.limeCode site phase :=
      congrArg Execution.Runtime.Config.code (DirectSequence.v1_to_lime s ctx.frame site phase)
    have tail :
        codeToLime (ctx.continuation.map (Sequence.emit v1Syntax)) = ctx.continuation.map (Sequence.emit limeSyntax) :=
      congrArg Execution.Runtime.Config.code (Sequence.v1_to_lime s ctx.sequence (.running [] ctx.continuation))
    change (⟨_, _, codeToLime (values ctx.saved ++ DirectSequence.v1Code site phase ++
      ctx.continuation.map (Sequence.emit v1Syntax))⟩ : Wasm.Lime1.Execution.Config H) = _
    rw [codeToLime_append, codeToLime_append, map_values, body, tail]
    rfl
  | continuation phase => exact Sequence.v1_to_lime s ctx.sequence phase

theorem lime_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} {ctx : Context} {p : Program}
    (g : LimeGuard s ctx p) (q : State ctx p.site) :
    (limeConfig s ctx p.site q).toCore = coreConfig s.toCore ctx p.site q := by
  open Wasm.Lime1.Execution in
  cases q with
  | active phase =>
    have body : Admin.listToCore s (DirectSequence.limeCode p.site phase) = DirectSequence.coreCode p.site phase :=
      congrArg Core.Config.code (DirectSequence.lime_to_core g.invocation phase)
    have tail : Admin.listToCore s (ctx.continuation.map (Sequence.emit limeSyntax)) =
        ctx.continuation.map (Sequence.emit coreSyntax) :=
      congrArg Core.Config.code (Sequence.lime_to_core g.continuation (.running [] ctx.continuation))
    change (⟨_, _, Admin.listToCore s (values ctx.saved ++ DirectSequence.limeCode p.site phase ++
      ctx.continuation.map (Sequence.emit limeSyntax))⟩ : Core.Config H) = _
    rw [CallContinuation.listToCore_append, CallContinuation.listToCore_append, CallContinuation.values_toCore,
      body, tail]
    rfl
  | continuation phase => exact Sequence.lime_to_core g.continuation phase

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Proofs
