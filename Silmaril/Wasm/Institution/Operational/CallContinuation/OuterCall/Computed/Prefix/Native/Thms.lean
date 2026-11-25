module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Thms
public import Silmaril.Wasm.Institution.Operational.CallFrame.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Core
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.V1

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix

open Execution
open Execution.Runtime (Frame Value)
open Wasm.Numerics (Profile)
open Wasm.SingleThreaded.Det (noHost)

/-! At a running prefix head or a trap, native readback retains the entire
configuration after the step. The suffix is arbitrary. A running prefix with
no remaining work leaves control to its suffix. -/

theorem v1_step_iff {H : Type} {s : Wasm.V1.Execution.Store H} {f : Frame}
    {stack : List Value} {op : Op} {tail : List Wasm.V1.Execution.Admin} {dst : Wasm.V1.Execution.Config H} :
    Wasm.V1.Execution.Step CallFrame.v1NoHost ⟨s, f, Wasm.V1.Execution.values stack ++ emit v1Syntax op :: tail⟩ dst ↔
      ∃ ans, Reduce f.locals stack op ans ∧
        dst = ⟨s, f, outcomeCode Wasm.V1.Execution.values .trap tail ans⟩ :=
  ⟨Proofs.V1.readback, fun ⟨_, reduction, eq⟩ => eq.symm ▸ Proofs.V1.sound reduction⟩

theorem lime_step_iff {H : Type} {s : Wasm.Lime1.Execution.Store H} {f : Frame}
    {stack : List Value} {op : Op} {tail : List Wasm.Lime1.Execution.Admin} {dst : Wasm.Lime1.Execution.Config H} :
    Wasm.Lime1.Execution.Step CallFrame.limeNoHost ⟨s, f, Wasm.Lime1.Execution.values stack ++ emit limeSyntax op :: tail⟩ dst ↔
      ∃ ans, Reduce f.locals stack op ans ∧
        dst = ⟨s, f, outcomeCode Wasm.Lime1.Execution.values .trap tail ans⟩ :=
  ⟨Computed.Proofs.Lime1.prefix_read, fun ⟨_, reduction, eq⟩ => eq.symm ▸ Computed.Proofs.Lime1.prefix_sound reduction⟩

theorem lime_discard_iff {A H : Type} {s : Wasm.Lime1.Execution.Store H} {f : Frame}
    (emitTail : A → Wasm.Lime1.Execution.Admin) {stack : List Value} {tail : List A} {dst : Wasm.Lime1.Execution.Config H} :
    Wasm.Lime1.Execution.Step CallFrame.limeNoHost ⟨s, f, Wasm.Lime1.Execution.values stack ++ .trap :: tail.map emitTail⟩ dst ↔
      ∃ kept rest, Discard stack tail kept rest ∧
        dst = ⟨s, f, Wasm.Lime1.Execution.values kept ++ .trap :: rest.map emitTail⟩ :=
  ⟨Computed.Proofs.Lime1.prefix_discard_read emitTail,
    fun ⟨_, _, reduction, eq⟩ => eq.symm ▸ Computed.Proofs.Lime1.prefix_discard_sound emitTail reduction⟩

theorem core_step_iff {H : Type} {P : Profile} {s : Core.Store H} {f : Frame}
    {stack : List Value} {op : Op} {tail : List Core.Admin} {dst : Core.Config H} :
    Core.Step P noHost ⟨s, f.toCore, coreValues stack ++ emit coreSyntax op :: tail⟩ dst ↔
      ∃ ans, Reduce f.locals stack op ans ∧
        dst = ⟨s, f.toCore, outcomeCode coreValues .trap tail ans⟩ :=
  ⟨Computed.Proofs.Core.prefix_read, fun ⟨_, reduction, eq⟩ => eq.symm ▸ Computed.Proofs.Core.prefix_sound reduction⟩

theorem core_discard_iff {A H : Type} {P : Profile} {s : Core.Store H} {f : Frame}
    (emitTail : A → Core.Admin) {stack : List Value} {tail : List A} {dst : Core.Config H} :
    Core.Step P noHost ⟨s, f.toCore, coreValues stack ++ .trap :: tail.map emitTail⟩ dst ↔
      ∃ kept rest, Discard stack tail kept rest ∧
        dst = ⟨s, f.toCore, coreValues kept ++ .trap :: rest.map emitTail⟩ :=
  ⟨Computed.Proofs.Core.prefix_discard_read emitTail,
    fun ⟨_, _, reduction, eq⟩ => eq.symm ▸ Computed.Proofs.Core.prefix_discard_sound emitTail reduction⟩

theorem v1_discard_iff {A H : Type} {s : Wasm.V1.Execution.Store H} {f : Frame}
    (emitTail : A → Wasm.V1.Execution.Admin) {stack : List Value} {tail : List A} {dst : Wasm.V1.Execution.Config H} :
    Wasm.V1.Execution.Step CallFrame.v1NoHost ⟨s, f, Wasm.V1.Execution.values stack ++ .trap :: tail.map emitTail⟩ dst ↔
      ∃ kept rest, Discard stack tail kept rest ∧
        dst = ⟨s, f, Wasm.V1.Execution.values kept ++ .trap :: rest.map emitTail⟩ :=
  ⟨Proofs.V1.discard_readback emitTail, fun ⟨_, _, cut, eq⟩ => eq.symm ▸ Proofs.V1.discard_sound emitTail cut⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix
