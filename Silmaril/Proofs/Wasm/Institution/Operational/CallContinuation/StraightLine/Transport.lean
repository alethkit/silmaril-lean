module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Transport
import Silmaril.Wasm.RuntimeMap.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Proofs

open Execution
open Execution.Runtime (Frame)
open OuterCall (coreValues)
open OuterCall.Computed

theorem guard_to_lime {H : Type} {s : Wasm.V1.Execution.Store H} {site : Site}
    (g : V1Guard s site) : LimeGuard (s.mapCode Wasm.V1.Func.toLime) site :=
  ⟨g.lookup, CallFrame.allocated_toLime g.allocated⟩

theorem guard_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} {site : Site}
    (g : LimeGuard s site) : CoreGuard s.toCore site :=
  ⟨g.lookup, CallFrame.allocated_toCore g.allocated⟩

private theorem prefix_to_lime (rest : List Prefix.Op) :
    Wasm.V1.Execution.codeToLime (rest.map (Prefix.emit v1Syntax)) = rest.map (Prefix.emit limeSyntax) := by
  induction rest with
  | nil => rfl
  | cons op rest ih =>
    simp only [List.map_cons, Wasm.V1.Execution.codeToLime_cons, ih]
    cases op <;> rfl

private theorem prefix_to_core {H : Type} (s : Wasm.Lime1.Execution.Store H) (rest : List Prefix.Op) :
    Wasm.Lime1.Execution.Admin.listToCore s (rest.map (Prefix.emit limeSyntax)) =
      rest.map (Prefix.emit coreSyntax) := by
  induction rest with
  | nil => rfl
  | cons op rest ih =>
    change Wasm.Lime1.Execution.Admin.toCore s (Prefix.emit limeSyntax op) ++
      Wasm.Lime1.Execution.Admin.listToCore s (rest.map (Prefix.emit limeSyntax)) = _
    rw [ih]
    cases op <;> rfl

private theorem body_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (site : Site) (q : State) :
    Wasm.V1.Execution.codeToLime (v1Body site q) = limeBody site q := by
  open Wasm.V1.Execution in
  cases q with
  | call saved args =>
    change codeToLime (values (saved ++ args) ++ .source (.call site.index) ::
      site.continuation.map (Prefix.emit v1Syntax)) = _
    rw [codeToLime_append, map_values, codeToLime_cons, prefix_to_lime]
    rfl
  | active phase =>
    have callee := congrArg Runtime.Config.code (CallFrame.v1_to_lime s site.outer site.address site.callee phase)
    change codeToLime (CallFrame.v1Code site.address site.callee phase) =
      CallFrame.limeCode site.address site.callee phase at callee
    change codeToLime (CallFrame.v1Code site.address site.callee phase ++ site.continuation.map (Prefix.emit v1Syntax)) = _
    rw [codeToLime_append, callee, prefix_to_lime]
    rfl
  | resume stack rest =>
    change codeToLime (values stack ++ rest.map (Prefix.emit v1Syntax)) = _
    rw [codeToLime_append, map_values, prefix_to_lime]
    rfl
  | trapped stack rest =>
    change codeToLime (values stack ++ .trap :: rest.map (Prefix.emit v1Syntax)) = _
    rw [codeToLime_append, map_values, codeToLime_cons, prefix_to_lime]
    rfl
  | boundary => rfl

private theorem body_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} {site : Site}
    (g : LimeGuard s site) (q : State) :
    Wasm.Lime1.Execution.Admin.listToCore s (limeBody site q) = coreBody site q := by
  open Wasm.Lime1.Execution in
  cases q with
  | call saved args =>
    change Admin.listToCore s (values (saved ++ args) ++ .source (.call site.index) ::
      site.continuation.map (Prefix.emit limeSyntax)) = _
    rw [CallContinuation.Proofs.core_append, CallContinuation.Proofs.core_values]
    change coreValues (saved ++ args) ++ .plain (.call site.index) ::
      Admin.listToCore s (site.continuation.map (Prefix.emit limeSyntax)) = _
    rw [prefix_to_core]
    rfl
  | active phase =>
    have callee := congrArg Core.Config.code (CallFrame.lime_to_core site.outer g.allocated phase)
    change Admin.listToCore s (CallFrame.limeCode site.address site.callee phase) =
      CallFrame.coreCode site.address site.callee phase at callee
    change Admin.listToCore s (CallFrame.limeCode site.address site.callee phase ++
      site.continuation.map (Prefix.emit limeSyntax)) = _
    rw [CallContinuation.Proofs.core_append, callee, prefix_to_core]
    rfl
  | resume stack rest =>
    change Admin.listToCore s (values stack ++ rest.map (Prefix.emit limeSyntax)) = _
    rw [CallContinuation.Proofs.core_append, CallContinuation.Proofs.core_values, prefix_to_core]
    rfl
  | trapped stack rest =>
    change Admin.listToCore s (values stack ++ .trap :: rest.map (Prefix.emit limeSyntax)) = _
    rw [CallContinuation.Proofs.core_append, CallContinuation.Proofs.core_values]
    change coreValues stack ++ .trap :: Admin.listToCore s (rest.map (Prefix.emit limeSyntax)) = _
    rw [prefix_to_core]
    rfl
  | boundary => rfl

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (caller : Frame) (site : Site) (q : State) :
    (v1Config s caller site q).toLime = limeConfig (s.mapCode Wasm.V1.Func.toLime) caller site q := by
  cases q with
  | boundary phase => exact Nested.v1_to_lime s caller site.outer site.address site.callee site.arity phase
  | _ =>
    exact congrArg (fun body => (⟨s.mapCode Wasm.V1.Func.toLime, caller,
      [.frame site.arity site.outer [.label site.arity [] body]]⟩ : Wasm.Lime1.Execution.Config H))
      (body_to_lime s site _)

theorem lime_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame} {site : Site}
    (g : LimeGuard s site) (q : State) :
    (limeConfig s caller site q).toCore = coreConfig s.toCore caller site q := by
  cases q with
  | boundary phase => exact Nested.lime_to_core caller site.outer g.allocated site.arity phase
  | _ =>
    exact congrArg (fun body => (⟨s.toCore, caller.toCore,
      [.frame site.arity site.outer.toCore [.label site.arity [] body]]⟩ : Core.Config H))
      (body_to_core g _)

end Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Proofs
