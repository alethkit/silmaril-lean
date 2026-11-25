module

public import Silmaril.Wasm.Execution.Core.Inversion.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Thms
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Nested.V1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Nested.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Nested.Core
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Nested.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Nested.Transport

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.Nested

open Execution
open Execution.Runtime (Frame FuncAddr Value)
open Wasm.SingleThreaded.Det (noHost)

theorem core_label_result {arity : Nat} {r : Result} {out : List Core.Admin}
    (pop : Core.LabelExit arity [] (resultCode (fun vs => Core.vals (vs.map Value.toCore)) .trap r) out) :
    out = resultCode (fun vs => Core.vals (vs.map Value.toCore)) .trap r :=
  Proofs.core_label_result pop

theorem core_frame_result {H : Type} {P : Numerics.Profile} {s : Core.Store H}
    {caller outer : Frame} {arity : Nat} {r : Result} {dst : Core.Config H}
    (step : Core.Step P noHost
      ⟨s, caller.toCore, [.frame arity outer.toCore (resultCode (fun vs => Core.vals (vs.map Value.toCore)) .trap r)]⟩ dst) :
    dst = ⟨s, caller.toCore, resultCode (fun vs => Core.vals (vs.map Value.toCore)) .trap r⟩ :=
  Proofs.core_frame_result step

theorem core_result_stuck {H : Type} {P : Numerics.Profile} {s : Core.Store H} {f : Core.Frame} {r : Result}
    {dst : Core.Config H}
    (step : Core.Step P noHost ⟨s, f, resultCode (fun vs => Core.vals (vs.map Value.toCore)) .trap r⟩ dst) : False :=
  Proofs.no_result_step step

open Wasm.Lime1.Execution in
theorem lime_label_result {types : List Wasm.Lime1.FuncType} {arity : Nat} {r : Result} {out : List Admin}
    (pop : PureStep types [.label arity [] (resultCode values .trap r)] out) :
    out = resultCode values .trap r :=
  Proofs.Lime1.label_result pop

open Wasm.Lime1.Execution in
theorem lime_frame_result {H : Type} {s : Store H} {caller outer : Frame} {arity : Nat} {r : Result}
    {dst : Config H} (step : Step CallFrame.limeNoHost ⟨s, caller, [.frame arity outer (resultCode values .trap r)]⟩ dst) :
    dst = ⟨s, caller, resultCode values .trap r⟩ :=
  Proofs.Lime1.frame_result step

open Wasm.Lime1.Execution in
theorem lime_result_stuck {H : Type} {s : Store H} {f : Frame} {r : Result} {dst : Config H}
    (step : Step CallFrame.limeNoHost ⟨s, f, resultCode values .trap r⟩ dst) : False :=
  Proofs.Lime1.result_stuck step

section v1
variable {H : Type} {s : Wasm.V1.Execution.Store H}
  {caller outer : Frame} {addr : FuncAddr} {fn : CallFrame.Callee} {arity : Nat}

theorem v1_sound (allocated : s.funcs[addr.value]? = some (.wasm fn.type fn.module fn.v1Func))
    {a b : State} (edge : Edge fn arity a b) :
    Wasm.V1.Execution.Step CallFrame.v1NoHost (v1Config s caller outer addr fn arity a) (v1Config s caller outer addr fn arity b) :=
  Proofs.V1.sound allocated edge

theorem v1_step_iff (allocated : s.funcs[addr.value]? = some (.wasm fn.type fn.module fn.v1Func))
    {a : State} {b : Wasm.V1.Execution.Config H} (guard : Admitted fn a) :
    Wasm.V1.Execution.Step CallFrame.v1NoHost (v1Config s caller outer addr fn arity a) b ↔
      ∃ out, Edge fn arity a out ∧ b = v1Config s caller outer addr fn arity out :=
  ⟨Proofs.V1.readback allocated guard, fun ⟨_, edge, eq⟩ => eq.symm ▸ v1_sound allocated edge⟩

theorem v1_run_iff (allocated : s.funcs[addr.value]? = some (.wasm fn.type fn.module fn.v1Func))
    {a : State} {b : Wasm.V1.Execution.Config H} (guard : Admitted fn a) :
    Relation.ReflTransGen (Wasm.V1.Execution.Step CallFrame.v1NoHost) (v1Config s caller outer addr fn arity a) b ↔
      ∃ out, Runs fn arity a out ∧ Admitted fn out ∧ b = v1Config s caller outer addr fn arity out :=
  Proofs.run_iff (v1Config s caller outer addr fn arity) _ (fun e => v1_sound allocated e)
    (fun h step => (v1_step_iff allocated h).mp step) guard

end v1

section lime
variable {H : Type} {s : Wasm.Lime1.Execution.Store H}
  {caller outer : Frame} {addr : FuncAddr} {fn : CallFrame.Callee} {arity : Nat}

theorem lime_sound (allocated : s.funcs[addr.value]? = some (.wasm fn.type fn.module fn.limeFunc))
    {a b : State} (edge : Edge fn arity a b) :
    Wasm.Lime1.Execution.Step CallFrame.limeNoHost (limeConfig s caller outer addr fn arity a) (limeConfig s caller outer addr fn arity b) :=
  Proofs.Lime1.sound allocated edge

theorem lime_step_iff (allocated : s.funcs[addr.value]? = some (.wasm fn.type fn.module fn.limeFunc))
    {a : State} {b : Wasm.Lime1.Execution.Config H} (guard : Admitted fn a) :
    Wasm.Lime1.Execution.Step CallFrame.limeNoHost (limeConfig s caller outer addr fn arity a) b ↔
      ∃ out, Edge fn arity a out ∧ b = limeConfig s caller outer addr fn arity out :=
  ⟨Proofs.Lime1.readback allocated guard, fun ⟨_, edge, eq⟩ => eq.symm ▸ lime_sound allocated edge⟩

theorem lime_run_iff (allocated : s.funcs[addr.value]? = some (.wasm fn.type fn.module fn.limeFunc))
    {a : State} {b : Wasm.Lime1.Execution.Config H} (guard : Admitted fn a) :
    Relation.ReflTransGen (Wasm.Lime1.Execution.Step CallFrame.limeNoHost) (limeConfig s caller outer addr fn arity a) b ↔
      ∃ out, Runs fn arity a out ∧ Admitted fn out ∧ b = limeConfig s caller outer addr fn arity out :=
  Proofs.run_iff (limeConfig s caller outer addr fn arity) _ (fun e => lime_sound allocated e)
    (fun h step => (lime_step_iff allocated h).mp step) guard

end lime

section core
variable {H : Type} {P : Numerics.Profile} {s : Core.Store H}
  {caller outer : Frame} {addr : FuncAddr} {fn : CallFrame.Callee} {arity : Nat}

theorem core_sound (allocated : s.funcs[addr.value]? = some fn.coreInstance)
    {a b : State} (edge : Edge fn arity a b) :
    Core.Step P noHost (coreConfig s caller outer addr fn arity a) (coreConfig s caller outer addr fn arity b) :=
  Proofs.core_sound allocated edge

theorem core_step_iff (allocated : s.funcs[addr.value]? = some fn.coreInstance)
    {a : State} {b : Core.Config H} (guard : Admitted fn a) :
    Core.Step P noHost (coreConfig s caller outer addr fn arity a) b ↔
      ∃ out, Edge fn arity a out ∧ b = coreConfig s caller outer addr fn arity out :=
  ⟨Proofs.core_readback allocated guard, fun ⟨_, edge, eq⟩ => eq.symm ▸ core_sound allocated edge⟩

theorem core_run_iff (allocated : s.funcs[addr.value]? = some fn.coreInstance)
    {a : State} {b : Core.Config H} (guard : Admitted fn a) :
    Relation.ReflTransGen (Core.Step P noHost) (coreConfig s caller outer addr fn arity a) b ↔
      ∃ out, Runs fn arity a out ∧ Admitted fn out ∧ b = coreConfig s caller outer addr fn arity out :=
  Proofs.run_iff (coreConfig s caller outer addr fn arity) _ (fun e => core_sound allocated e)
    (fun h step => (core_step_iff allocated h).mp step) guard

end core

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (caller outer : Frame)
    (addr : FuncAddr) (fn : CallFrame.Callee) (arity : Nat) (q : State) :
    (v1Config s caller outer addr fn arity q).toLime =
      limeConfig (s.mapCode Wasm.V1.Func.toLime) caller outer addr fn arity q :=
  Proofs.v1_to_lime s caller outer addr fn arity q

theorem lime_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} (caller outer : Frame)
    {addr : FuncAddr} {fn : CallFrame.Callee}
    (allocated : s.funcs[addr.value]? = some (.wasm fn.type fn.module fn.limeFunc)) (arity : Nat) (q : State) :
    (limeConfig s caller outer addr fn arity q).toCore = coreConfig s.toCore caller outer addr fn arity q :=
  Proofs.lime_to_core caller outer allocated arity q

end Silmaril.Wasm.Institution.Operational.CallContinuation.Nested
