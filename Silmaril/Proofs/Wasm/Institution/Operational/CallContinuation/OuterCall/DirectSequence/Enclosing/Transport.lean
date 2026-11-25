module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Native.Defs
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Proofs

open Execution
open Computed (v1Syntax limeSyntax coreSyntax)
open Computed.Prefix (Op emit)

private theorem ops_to_lime (rest : List Op) :
    Wasm.V1.Execution.codeToLime (rest.map (emit v1Syntax)) = rest.map (emit limeSyntax) := by
  induction rest with
  | nil => rfl
  | cons op rest ih =>
    simp only [List.map_cons, Wasm.V1.Execution.codeToLime_cons, ih]
    cases op <;> rfl

private theorem ops_to_core {H : Type} (s : Wasm.Lime1.Execution.Store H) (rest : List Op) :
    Wasm.Lime1.Execution.Admin.listToCore s (rest.map (emit limeSyntax)) = rest.map (emit coreSyntax) := by
  induction rest with
  | nil => rfl
  | cons op rest ih =>
    change Wasm.Lime1.Execution.Admin.toCore s (emit limeSyntax op) ++
      Wasm.Lime1.Execution.Admin.listToCore s (rest.map (emit limeSyntax)) = _
    rw [ih]
    cases op <;> rfl

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (ctx : Context) (site : Site) (q : State site) :
    (v1Config s ctx site q).toLime = limeConfig (s.mapCode Wasm.V1.Func.toLime) ctx site q := by
  open Wasm.V1.Execution in
  cases q with
  | active phase =>
    have body : codeToLime (DirectSequence.v1Code site phase) = DirectSequence.limeCode site phase :=
      congrArg Execution.Runtime.Config.code (DirectSequence.v1_to_lime s ctx.frame site phase)
    change (⟨_, _, codeToLime (values ctx.saved ++ DirectSequence.v1Code site phase ++
      ctx.continuation.map (emit v1Syntax))⟩ : Wasm.Lime1.Execution.Config H) = _
    rw [codeToLime_append, codeToLime_append, map_values, body, ops_to_lime]
    rfl
  | resume stack rest =>
    change (⟨_, _, codeToLime (values stack ++ rest.map (emit v1Syntax))⟩ : Wasm.Lime1.Execution.Config H) = _
    rw [codeToLime_append, map_values, ops_to_lime]
    rfl
  | trapped stack rest =>
    change (⟨_, _, codeToLime (values stack ++ .trap :: rest.map (emit v1Syntax))⟩ : Wasm.Lime1.Execution.Config H) = _
    rw [codeToLime_append, map_values, codeToLime_cons, ops_to_lime]
    rfl

theorem lime_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} {ctx : Context} {p : Program}
    (g : DirectSequence.LimeGuard s ctx.frame p) (q : State p.site) :
    (limeConfig s ctx p.site q).toCore = coreConfig s.toCore ctx p.site q := by
  open Wasm.Lime1.Execution in
  cases q with
  | active phase =>
    have body : Admin.listToCore s (DirectSequence.limeCode p.site phase) = DirectSequence.coreCode p.site phase :=
      congrArg Core.Config.code (DirectSequence.lime_to_core g phase)
    change (⟨_, _, Admin.listToCore s (values ctx.saved ++ DirectSequence.limeCode p.site phase ++
      ctx.continuation.map (emit limeSyntax))⟩ : Core.Config H) = _
    rw [CallContinuation.listToCore_append, CallContinuation.listToCore_append, CallContinuation.values_toCore,
      body, ops_to_core]
    rfl
  | resume stack rest =>
    change (⟨_, _, Admin.listToCore s (values stack ++ rest.map (emit limeSyntax))⟩ : Core.Config H) = _
    rw [CallContinuation.listToCore_append, CallContinuation.values_toCore, ops_to_core]
    rfl
  | trapped stack rest =>
    change (⟨_, _, Admin.listToCore s (values stack ++ .trap :: rest.map (emit limeSyntax))⟩ : Core.Config H) = _
    rw [CallContinuation.listToCore_append, CallContinuation.values_toCore]
    change (⟨_, _, coreValues stack ++ .trap :: Admin.listToCore s (rest.map (emit limeSyntax))⟩ : Core.Config H) = _
    rw [ops_to_core]
    rfl

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Proofs
