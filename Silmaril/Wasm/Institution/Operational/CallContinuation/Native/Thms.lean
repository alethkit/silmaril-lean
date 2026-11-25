module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Thms
public import Silmaril.Wasm.Institution.Operational.CallFrame.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.V1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Core
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Transport

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation

open Execution
open Execution.Runtime (Frame FuncAddr)
open Wasm.SingleThreaded.Det (noHost)

section v1
variable {H : Type} {s : Wasm.V1.Execution.Store H}
  {caller : Frame} {addr : FuncAddr} {fn : CallFrame.Callee}

theorem v1_sound (allocated : s.funcs[addr.value]? = some (.wasm fn.type fn.module fn.v1Func))
    {a b : State} (edge : Edge fn a b) :
    Wasm.V1.Execution.Step CallFrame.v1NoHost (v1Config s caller addr fn a) (v1Config s caller addr fn b) :=
  Proofs.V1.sound allocated edge

theorem v1_step_iff (allocated : s.funcs[addr.value]? = some (.wasm fn.type fn.module fn.v1Func))
    {a : State} {b : Wasm.V1.Execution.Config H} (guard : Admitted fn a) :
    Wasm.V1.Execution.Step CallFrame.v1NoHost (v1Config s caller addr fn a) b ↔
      ∃ out, Edge fn a out ∧ b = v1Config s caller addr fn out :=
  ⟨Proofs.V1.readback allocated guard, fun ⟨_, edge, eq⟩ => eq.symm ▸ v1_sound allocated edge⟩

theorem v1_run_iff (allocated : s.funcs[addr.value]? = some (.wasm fn.type fn.module fn.v1Func))
    {a : State} {b : Wasm.V1.Execution.Config H} (guard : Admitted fn a) :
    Relation.ReflTransGen (Wasm.V1.Execution.Step CallFrame.v1NoHost) (v1Config s caller addr fn a) b ↔
      ∃ out, Runs fn a out ∧ Admitted fn out ∧ b = v1Config s caller addr fn out :=
  Proofs.run_iff (v1Config s caller addr fn) _ (fun e => v1_sound allocated e)
    (fun h step => (v1_step_iff allocated h).mp step) guard

end v1

section lime
variable {H : Type} {s : Wasm.Lime1.Execution.Store H}
  {caller : Frame} {addr : FuncAddr} {fn : CallFrame.Callee}

theorem lime_sound (allocated : s.funcs[addr.value]? = some (.wasm fn.type fn.module fn.limeFunc))
    {a b : State} (edge : Edge fn a b) :
    Wasm.Lime1.Execution.Step CallFrame.limeNoHost (limeConfig s caller addr fn a) (limeConfig s caller addr fn b) :=
  Proofs.Lime1.sound allocated edge

theorem lime_step_iff (allocated : s.funcs[addr.value]? = some (.wasm fn.type fn.module fn.limeFunc))
    {a : State} {b : Wasm.Lime1.Execution.Config H} (guard : Admitted fn a) :
    Wasm.Lime1.Execution.Step CallFrame.limeNoHost (limeConfig s caller addr fn a) b ↔
      ∃ out, Edge fn a out ∧ b = limeConfig s caller addr fn out :=
  ⟨Proofs.Lime1.readback allocated guard, fun ⟨_, edge, eq⟩ => eq.symm ▸ lime_sound allocated edge⟩

theorem lime_run_iff (allocated : s.funcs[addr.value]? = some (.wasm fn.type fn.module fn.limeFunc))
    {a : State} {b : Wasm.Lime1.Execution.Config H} (guard : Admitted fn a) :
    Relation.ReflTransGen (Wasm.Lime1.Execution.Step CallFrame.limeNoHost) (limeConfig s caller addr fn a) b ↔
      ∃ out, Runs fn a out ∧ Admitted fn out ∧ b = limeConfig s caller addr fn out :=
  Proofs.run_iff (limeConfig s caller addr fn) _ (fun e => lime_sound allocated e)
    (fun h step => (lime_step_iff allocated h).mp step) guard

end lime

section core
variable {H : Type} {P : Numerics.Profile} {s : Core.Store H}
  {caller : Frame} {addr : FuncAddr} {fn : CallFrame.Callee}

theorem core_sound (allocated : s.funcs[addr.value]? = some fn.coreInstance)
    {a b : State} (edge : Edge fn a b) :
    Core.Step P noHost (coreConfig s caller addr fn a) (coreConfig s caller addr fn b) :=
  Proofs.core_sound allocated edge

theorem core_step_iff (allocated : s.funcs[addr.value]? = some fn.coreInstance)
    {a : State} {b : Core.Config H} (guard : Admitted fn a) :
    Core.Step P noHost (coreConfig s caller addr fn a) b ↔
      ∃ out, Edge fn a out ∧ b = coreConfig s caller addr fn out :=
  ⟨Proofs.core_readback allocated guard, fun ⟨_, edge, eq⟩ => eq.symm ▸ core_sound allocated edge⟩

theorem core_run_iff (allocated : s.funcs[addr.value]? = some fn.coreInstance)
    {a : State} {b : Core.Config H} (guard : Admitted fn a) :
    Relation.ReflTransGen (Core.Step P noHost) (coreConfig s caller addr fn a) b ↔
      ∃ out, Runs fn a out ∧ Admitted fn out ∧ b = coreConfig s caller addr fn out :=
  Proofs.run_iff (coreConfig s caller addr fn) _ (fun e => core_sound allocated e)
    (fun h step => (core_step_iff allocated h).mp step) guard

end core

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (caller : Frame)
    (addr : FuncAddr) (fn : CallFrame.Callee) (q : State) :
    (v1Config s caller addr fn q).toLime =
      limeConfig (s.mapCode Wasm.V1.Func.toLime) caller addr fn q :=
  Proofs.v1_to_lime s caller addr fn q

theorem lime_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} (caller : Frame)
    {addr : FuncAddr} {fn : CallFrame.Callee}
    (allocated : s.funcs[addr.value]? = some (.wasm fn.type fn.module fn.limeFunc)) (q : State) :
    (limeConfig s caller addr fn q).toCore = coreConfig s.toCore caller addr fn q :=
  Proofs.lime_to_core caller allocated q

end Silmaril.Wasm.Institution.Operational.CallContinuation
