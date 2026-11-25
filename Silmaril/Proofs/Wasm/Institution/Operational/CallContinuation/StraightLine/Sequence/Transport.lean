module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Native.Defs
import Silmaril.Wasm.Institution.Operational.CallFrame.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Proofs

open Execution
open OuterCall (coreValues)
open OuterCall.Computed

theorem guard_to_lime {H : Type} {s : Wasm.V1.Execution.Store H} {site : Site} (g : V1Guard s site) :
    LimeGuard (s.mapCode Wasm.V1.Func.toLime) site :=
  ⟨g.readOnly, g.typed, g.resolves, fun i => CallFrame.allocated_toLime (g.allocated i)⟩

theorem guard_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} {site : Site} (g : LimeGuard s site) :
    CoreGuard s.toCore site :=
  ⟨g.readOnly, g.typed, g.resolves, fun i => CallFrame.allocated_toCore (g.allocated i)⟩

private theorem code_to_lime {site : Site} (rest : List (Op site)) :
    Wasm.V1.Execution.codeToLime (rest.map (emit v1Syntax)) = rest.map (emit limeSyntax) := by
  induction rest with
  | nil => rfl
  | cons op rest ih =>
    simp only [List.map_cons, Wasm.V1.Execution.codeToLime_cons, ih]
    cases op with
    | numeric op => cases op <;> rfl
    | call => rfl

private theorem code_to_core {H : Type} (s : Wasm.Lime1.Execution.Store H) {site : Site} (rest : List (Op site)) :
    Wasm.Lime1.Execution.Admin.listToCore s (rest.map (emit limeSyntax)) = rest.map (emit coreSyntax) := by
  induction rest with
  | nil => rfl
  | cons op rest ih =>
    change Wasm.Lime1.Execution.Admin.toCore s (emit limeSyntax op) ++
      Wasm.Lime1.Execution.Admin.listToCore s (rest.map (emit limeSyntax)) = _
    rw [ih]
    cases op with
    | numeric op => cases op <;> rfl
    | call => rfl

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (site : Site) (q : State site) :
    (v1Config s site q).toLime = limeConfig (s.mapCode Wasm.V1.Func.toLime) site q := by
  open Wasm.V1.Execution in
  cases q with
  | running stack rest =>
    change (⟨s.mapCode Wasm.V1.Func.toLime, site.frame, codeToLime (values stack ++ rest.map (emit v1Syntax))⟩ :
      Wasm.Lime1.Execution.Config H) = _
    rw [codeToLime_append, map_values, code_to_lime]
    rfl
  | active i phase rest =>
    let target := site.target i
    have lifted := congrArg Runtime.Config.code (CallFrame.v1_to_lime s site.frame target.address target.callee phase)
    change codeToLime (CallFrame.v1Code target.address target.callee phase) =
      CallFrame.limeCode target.address target.callee phase at lifted
    change (⟨s.mapCode Wasm.V1.Func.toLime, site.frame,
      codeToLime (CallFrame.v1Code target.address target.callee phase ++ rest.map (emit v1Syntax))⟩ :
        Wasm.Lime1.Execution.Config H) = _
    rw [codeToLime_append, lifted, code_to_lime]
    rfl
  | trapped stack rest =>
    change (⟨s.mapCode Wasm.V1.Func.toLime, site.frame, codeToLime (values stack ++ .trap :: rest.map (emit v1Syntax))⟩ :
      Wasm.Lime1.Execution.Config H) = _
    rw [codeToLime_append, map_values, codeToLime_cons, code_to_lime]
    rfl

theorem lime_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} {site : Site}
    (g : LimeGuard s site) (q : State site) : (limeConfig s site q).toCore = coreConfig s.toCore site q := by
  open Wasm.Lime1.Execution in
  cases q with
  | running stack rest =>
    change (⟨s.toCore, site.frame.toCore, Admin.listToCore s (values stack ++ rest.map (emit limeSyntax))⟩ :
      Core.Config H) = _
    rw [CallContinuation.listToCore_append, CallContinuation.values_toCore, code_to_core]
    rfl
  | active i phase rest =>
    let target := site.target i
    have lifted := congrArg Core.Config.code (CallFrame.lime_to_core site.frame (g.allocated i) phase)
    change Admin.listToCore s (CallFrame.limeCode target.address target.callee phase) =
      CallFrame.coreCode target.address target.callee phase at lifted
    change (⟨s.toCore, site.frame.toCore,
      Admin.listToCore s (CallFrame.limeCode target.address target.callee phase ++ rest.map (emit limeSyntax))⟩ :
        Core.Config H) = _
    rw [CallContinuation.listToCore_append, lifted, code_to_core]
    rfl
  | trapped stack rest =>
    change (⟨s.toCore, site.frame.toCore, Admin.listToCore s (values stack ++ .trap :: rest.map (emit limeSyntax))⟩ :
      Core.Config H) = _
    rw [CallContinuation.listToCore_append, CallContinuation.values_toCore]
    change (⟨s.toCore, site.frame.toCore, coreValues stack ++ .trap :: Admin.listToCore s (rest.map (emit limeSyntax))⟩ :
      Core.Config H) = _
    rw [code_to_core]
    rfl

end Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Proofs
