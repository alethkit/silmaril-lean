module

public import Silmaril.Wasm.Institution.Operational.CallFrame.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallFrame.Thms
public import Silmaril.Wasm.SingleThreaded.Determinism.Head
import Silmaril.Proofs.Wasm.Institution.Operational.CallFrame.Core
import Silmaril.Proofs.Wasm.Institution.Operational.CallFrame.V1
import Silmaril.Proofs.Wasm.Institution.Operational.CallFrame.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.CallFrame.Transport

/-! Exact native readback from a guarded, resolved numeric call. The renderers
retain the store and caller frame and distinguish returned values from a trap. -/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallFrame

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (Frame FuncAddr)
open Silmaril.Wasm.SingleThreaded.Det (noHost)

section V1
variable {H : Type} {s : Wasm.V1.Execution.Store H}
variable {caller : Frame} {address : FuncAddr} {fn : Callee}

theorem v1_sound (allocated : s.funcs[address.value]? = some (.wasm fn.type fn.module fn.v1Func))
    {a b : State} (edge : Edge fn a b) :
    Wasm.V1.Execution.Step v1NoHost (v1Config s caller address fn a) (v1Config s caller address fn b) :=
  Proofs.V1.sound allocated edge

theorem v1_step_iff (allocated : s.funcs[address.value]? = some (.wasm fn.type fn.module fn.v1Func))
    {a : State} {target : Wasm.V1.Execution.Config H} (ready : Admitted fn a) :
    Wasm.V1.Execution.Step v1NoHost (v1Config s caller address fn a) target ↔
      ∃ out, Edge fn a out ∧ target = v1Config s caller address fn out :=
  ⟨Proofs.V1.readback allocated ready, fun ⟨_, step, eq⟩ => eq.symm ▸ v1_sound allocated step⟩

theorem v1_run_iff (allocated : s.funcs[address.value]? = some (.wasm fn.type fn.module fn.v1Func))
    {a : State} {target : Wasm.V1.Execution.Config H} (ready : Admitted fn a) :
    Relation.ReflTransGen (Wasm.V1.Execution.Step v1NoHost) (v1Config s caller address fn a) target ↔
      ∃ out, Runs fn a out ∧ Admitted fn out ∧ target = v1Config s caller address fn out :=
  Proofs.run_iff (v1Config s caller address fn) _ (fun h => v1_sound allocated h)
    (fun guard step => (v1_step_iff allocated guard).mp step) ready

end V1

section Lime1
variable {H : Type} {s : Wasm.Lime1.Execution.Store H}
variable {caller : Frame} {address : FuncAddr} {fn : Callee}

theorem lime_sound (allocated : s.funcs[address.value]? = some (.wasm fn.type fn.module fn.limeFunc))
    {a b : State} (edge : Edge fn a b) :
    Wasm.Lime1.Execution.Step limeNoHost (limeConfig s caller address fn a) (limeConfig s caller address fn b) :=
  Proofs.Lime1.sound allocated edge

theorem lime_step_iff (allocated : s.funcs[address.value]? = some (.wasm fn.type fn.module fn.limeFunc))
    {a : State} {target : Wasm.Lime1.Execution.Config H} (ready : Admitted fn a) :
    Wasm.Lime1.Execution.Step limeNoHost (limeConfig s caller address fn a) target ↔
      ∃ out, Edge fn a out ∧ target = limeConfig s caller address fn out :=
  ⟨Proofs.Lime1.readback allocated ready, fun ⟨_, step, eq⟩ => eq.symm ▸ lime_sound allocated step⟩

theorem lime_run_iff (allocated : s.funcs[address.value]? = some (.wasm fn.type fn.module fn.limeFunc))
    {a : State} {target : Wasm.Lime1.Execution.Config H} (ready : Admitted fn a) :
    Relation.ReflTransGen (Wasm.Lime1.Execution.Step limeNoHost) (limeConfig s caller address fn a) target ↔
      ∃ out, Runs fn a out ∧ Admitted fn out ∧ target = limeConfig s caller address fn out :=
  Proofs.run_iff (limeConfig s caller address fn) _ (fun h => lime_sound allocated h)
    (fun guard step => (lime_step_iff allocated guard).mp step) ready

/-- A fully supplied native Wasm invocation enters its frame and initial label in one step. -/
theorem lime_invoke_wasm_exact {ty : Wasm.Lime1.FuncType} {m : Execution.Runtime.ModuleInst}
    {fnCode : Wasm.Lime1.Func} {args : List Execution.Runtime.Value} {dst : Wasm.Lime1.Execution.Config H}
    (allocated : s.funcs[address.value]? = some (.wasm ty m fnCode)) (count : args.length = ty.params.length) :
    Wasm.Lime1.Execution.Step limeNoHost
      ⟨s, caller, Wasm.Lime1.Execution.values args ++ [.invoke address]⟩ dst ↔
      dst = ⟨s, caller, [.frame ty.results.length ⟨args ++ fnCode.locals.map Execution.Runtime.Value.zero, m⟩
        [.label ty.results.length [] (Wasm.Lime1.Execution.expression fnCode.body)]]⟩ :=
  Proofs.Lime1.invoke_wasm_exact allocated count

end Lime1

section Core
variable {H : Type} {P : Wasm.Numerics.Profile} {s : Core.Store H}
variable {caller : Frame} {address : FuncAddr} {fn : Callee}

theorem core_sound (allocated : s.funcs[address.value]? = some fn.coreInstance)
    {a b : State} (edge : Edge fn a b) :
    Core.Step P noHost (coreConfig s caller address fn a) (coreConfig s caller address fn b) :=
  Proofs.core_sound allocated edge

theorem core_step_iff (allocated : s.funcs[address.value]? = some fn.coreInstance)
    {a : State} {target : Core.Config H} (ready : Admitted fn a) :
    Core.Step P noHost (coreConfig s caller address fn a) target ↔
      ∃ out, Edge fn a out ∧ target = coreConfig s caller address fn out :=
  ⟨Proofs.core_readback allocated ready, fun ⟨_, step, eq⟩ => eq.symm ▸ core_sound allocated step⟩

theorem core_run_iff (allocated : s.funcs[address.value]? = some fn.coreInstance)
    {a : State} {target : Core.Config H} (ready : Admitted fn a) :
    Relation.ReflTransGen (Core.Step P noHost) (coreConfig s caller address fn a) target ↔
      ∃ out, Runs fn a out ∧ Admitted fn out ∧ target = coreConfig s caller address fn out :=
  Proofs.run_iff (coreConfig s caller address fn) _ (fun h => core_sound allocated h)
    (fun guard step => (core_step_iff allocated guard).mp step) ready

end Core

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (caller : Frame) (address : FuncAddr)
    (fn : Callee) (q : State) :
    (v1Config s caller address fn q).toLime =
      limeConfig (s.mapCode Wasm.V1.Func.toLime) caller address fn q :=
  Proofs.v1_to_lime s caller address fn q

theorem lime_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} (caller : Frame)
    {address : FuncAddr} {fn : Callee}
    (allocated : s.funcs[address.value]? = some (.wasm fn.type fn.module fn.limeFunc))
    (q : State) :
    (limeConfig s caller address fn q).toCore = coreConfig s.toCore caller address fn q :=
  Proofs.lime_to_core caller allocated q

theorem allocated_toLime {H : Type} {s : Wasm.V1.Execution.Store H} {address : FuncAddr} {fn : Callee}
    (h : s.funcs[address.value]? = some (.wasm fn.type fn.module fn.v1Func)) :
    (s.mapCode Wasm.V1.Func.toLime).funcs[address.value]? = some (.wasm fn.type fn.module fn.limeFunc) :=
  Proofs.allocated_toLime h

theorem allocated_toCore {H : Type} {s : Wasm.Lime1.Execution.Store H} {address : FuncAddr} {fn : Callee}
    (h : s.funcs[address.value]? = some (.wasm fn.type fn.module fn.limeFunc)) :
    s.toCore.funcs[address.value]? = some fn.coreInstance :=
  Proofs.allocated_toCore h

end Silmaril.Wasm.Institution.Operational.CallFrame
