module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume.Defs
public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume.Common
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume.Core
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume.Lime1

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume

open Execution
open Execution.Runtime (Frame Value)
open CallContinuation
open CallContinuation.OuterCall.Ranked
open Wasm.SingleThreaded.Det (noHost)

theorem resume_admitted {cont : Continuation} {program : Graph.Program} {caller : Frame}
    {saved : List Value} {results : List NumType} {result : Nested.Result}
    (checked : cont.Checked program caller saved results)
    (typed : match result with | .values xs => xs.map Value.type = results | .trap => True) :
    Graph.Admitted program cont.owner (cont.resume caller saved result) :=
  Proofs.resume_admitted checked typed

theorem of_callee_run {program : Graph.Program} {cont : Continuation} {call : Invocation}
    (checked : call.Checked program) {phase : Graph.Phase}
    (path : program.FrameRuns call.address call.entered phase) :
    Runs program call cont (.callee call.entered) (.callee phase) :=
  Proofs.of_callee_run checked path

/-- An exact native prefix accounts for every finite endpoint before entry.
After entry the ordinary native step relation takes over. -/
theorem prefix_run_iff {C : Type} {native : C → C → Prop} (before : List C) (entry : C) {dst : C}
    (chain : (before ++ [entry]).IsChain (fun a b => ∀ out, native a out ↔ out = b)) :
    Relation.ReflTransGen native (before.headD entry) dst ↔
      dst ∈ before ∨ Relation.ReflTransGen native entry dst :=
  Proofs.prefix_run_iff before entry chain

section Core

variable {H : Type} {P : Numerics.Profile} {s : Core.Store H} {program : Graph.Program}
  {call : Invocation} {cont : Continuation} {outer : Frame}

/-- Lift the exact lookup trace to the entered caller. On failure the last
configuration is the first native trap, with any pending lowering retained. -/
theorem core_resolution_allocated_exact {site : Indirect.Site} {caller : Frame} {out : Outcome}
    {selector : BitVec 32} {stack : List Value} {addr : Nat}
    (checked : site.check program caller = true) (allocated : site.CoreAllocated program s)
    (tableFound : s.table? caller.toCore tableIndex = some (addr, site.table.toCore))
    (resolved : site.resolve program selector = some out) :
    out.coreTrace.IsChain (fun a b => ∀ dst,
      Core.Step P noHost
        (cont.coreWrap outer (Indirect.coreConfig s caller site selector stack (cont.code.map Graph.coreEmit) a)) dst ↔
        dst = cont.coreWrap outer (Indirect.coreConfig s caller site selector stack (cont.code.map Graph.coreEmit) b)) :=
  Proofs.Core.resolution_prefix_exact checked allocated tableFound resolved

theorem core_resolution_prefix_exact {site : Indirect.Site} {caller : Frame} {out : Outcome}
    {selector : BitVec 32} {stack : List Value} {addr : Nat}
    (checked : site.check program caller = true) (allocated : program.CoreAllocated s)
    (tableFound : s.table? caller.toCore tableIndex = some (addr, site.table.toCore))
    (resolved : site.resolve program selector = some out) :
    out.coreTrace.IsChain (fun a b => ∀ dst,
      Core.Step P noHost
        (cont.coreWrap outer (Indirect.coreConfig s caller site selector stack (cont.code.map Graph.coreEmit) a)) dst ↔
        dst = cont.coreWrap outer (Indirect.coreConfig s caller site selector stack (cont.code.map Graph.coreEmit) b)) :=
  Proofs.Core.resolution_prefix_exact checked (fun a fn _ found => allocated a fn found) tableFound resolved

theorem core_entry_iff (checked : call.Checked program)
    (allocated : s.funcs[call.address.value]? = some call.callee.coreInstance) {dst : Core.Config H} :
    Core.Step P noHost (cont.coreWrap outer (Indirect.coreConfig s call.caller call.site call.selector (call.saved ++ call.args)
        (cont.code.map Graph.coreEmit) (.call (some call.address)))) dst ↔
      dst = cont.coreConfig call s outer (.callee call.entered) :=
  Proofs.Core.entry_iff checked allocated

theorem core_entered_run_iff (checked : call.Checked program) (allocated : program.CoreLinksAllocated s)
    (continuation : cont.Checked program call.caller call.saved call.site.signature.results)
    {dst : Core.Config H} :
    Core.Steps P noHost (cont.coreConfig call s outer (.callee call.entered)) dst ↔
      ∃ out, Runs program call cont (.callee call.entered) out ∧ dst = cont.coreConfig call s outer out :=
  Proofs.Core.entered_run_iff checked allocated continuation

theorem core_prefix_exact (checked : call.Checked program) (allocated : program.CoreAllocated s)
    {addr : Nat} (tableFound : s.table? call.caller.toCore tableIndex = some (addr, call.site.table.toCore)) :
    (cont.corePrefix call s outer).IsChain (fun a b => ∀ dst, Core.Step P noHost a dst ↔ dst = b) :=
  Proofs.Core.prefix_exact checked allocated tableFound

/-- Exact finite native readback from a successfully resolved designated site
through callee execution, the checked caller tail, and the caller function exit.
The outer frame's code is empty. -/
theorem core_run_iff (checked : call.Checked program) (allocated : program.CoreAllocated s)
    (continuation : cont.Checked program call.caller call.saved call.site.signature.results)
    {addr : Nat} (tableFound : s.table? call.caller.toCore tableIndex = some (addr, call.site.table.toCore))
    {dst : Core.Config H} :
    Core.Steps P noHost
      (cont.coreWrap outer (Indirect.coreConfig s call.caller call.site call.selector (call.saved ++ call.args)
        (cont.code.map Graph.coreEmit) .start)) dst ↔
      dst ∈ (cont.corePrefix call s outer).dropLast ∨
      ∃ out, Runs program call cont (.callee call.entered) out ∧ dst = cont.coreConfig call s outer out :=
  Proofs.Core.run_iff checked allocated continuation tableFound

end Core

section Lime1

open Wasm.Lime1.Execution

variable {H : Type} {s : Store H} {program : Graph.Program}
  {call : Invocation} {cont : Continuation} {outer : Frame}

theorem lime_resolution_allocated_iff {site : Indirect.Site} {caller : Frame} {selector : BitVec 32}
    {stack : List Value} {out : Outcome} {dst : Config H}
    (checked : site.check program caller = true) (allocated : site.LimeAllocated program s)
    (tableFound : frameTable s caller = some site.table) (resolved : site.resolve program selector = some out) :
    Step CallFrame.limeNoHost
      (cont.limeWrap outer (limeSource s caller site selector stack (cont.code.map Graph.limeEmit))) dst ↔
      dst = cont.limeWrap outer (limeResolved s caller stack (cont.code.map Graph.limeEmit) out) :=
  Proofs.Lime1.resolution_step_iff checked allocated tableFound resolved

theorem lime_resolution_step_iff {site : Indirect.Site} {caller : Frame} {selector : BitVec 32}
    {stack : List Value} {out : Outcome} {dst : Config H}
    (checked : site.check program caller = true) (allocated : program.LimeAllocated s)
    (tableFound : frameTable s caller = some site.table) (resolved : site.resolve program selector = some out) :
    Step CallFrame.limeNoHost
      (cont.limeWrap outer (limeSource s caller site selector stack (cont.code.map Graph.limeEmit))) dst ↔
      dst = cont.limeWrap outer (limeResolved s caller stack (cont.code.map Graph.limeEmit) out) :=
  Proofs.Lime1.resolution_step_iff checked (fun a fn _ found => allocated a fn found) tableFound resolved

theorem lime_entry_iff (checked : call.Checked program)
    (allocated : s.funcs[call.address.value]? = some (.wasm call.callee.declaration.type call.callee.declaration.module call.callee.limeFunc)) {dst : Config H} :
    Step CallFrame.limeNoHost (cont.limeWrap outer (Indirect.limeResolved s call.caller (call.saved ++ call.args) (cont.code.map Graph.limeEmit) (.resolved call.address))) dst ↔
      dst = cont.limeConfig call s outer (.callee call.entered) :=
  Proofs.Lime1.entry_iff checked allocated

theorem lime_entered_run_iff (checked : call.Checked program) (allocated : program.LimeLinksAllocated s)
    (continuation : cont.Checked program call.caller call.saved call.site.signature.results)
    {dst : Config H} :
    Steps CallFrame.limeNoHost (cont.limeConfig call s outer (.callee call.entered)) dst ↔
      ∃ out, Runs program call cont (.callee call.entered) out ∧ dst = cont.limeConfig call s outer out :=
  Proofs.Lime1.entered_run_iff checked allocated continuation

theorem lime_prefix_exact (checked : call.Checked program) (allocated : program.LimeAllocated s)
    (tableFound : frameTable s call.caller = some call.site.table) :
    (cont.limePrefix call s outer).IsChain (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) :=
  Proofs.Lime1.prefix_exact checked allocated tableFound

theorem lime_run_iff (checked : call.Checked program) (allocated : program.LimeAllocated s)
    (continuation : cont.Checked program call.caller call.saved call.site.signature.results)
    (tableFound : frameTable s call.caller = some call.site.table) {dst : Config H} :
    Steps CallFrame.limeNoHost
      (cont.limeWrap outer (limeSource s call.caller call.site call.selector (call.saved ++ call.args)
        (cont.code.map Graph.limeEmit))) dst ↔
      dst ∈ (cont.limePrefix call s outer).dropLast ∨
      ∃ out, Runs program call cont (.callee call.entered) out ∧ dst = cont.limeConfig call s outer out :=
  Proofs.Lime1.run_iff checked allocated continuation tableFound

end Lime1

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume
