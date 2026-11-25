module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Thms
public import Silmaril.Wasm.SingleThreaded.Determinism.Head
public import Silmaril.Wasm.Institution.Operational.CallFrame.Native.Defs
public import Silmaril.Wasm.Execution.Core.Inversion.Defs
public import Silmaril.Wasm.Lime1.Execution.Callout
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.Core
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.Lime1

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect

open Execution.Runtime (Frame Value)
open Execution
open CallContinuation.OuterCall.Ranked.Graph (Program Function)
open SingleThreaded.Det (noHost)

/-- A pending indirect operation reduces within an entered empty-continuation label. -/
theorem core_lookup_stays {site : Site} {selector : BitVec 32} {stack : List Value}
    {rest : List Core.Admin} {phase : Phase} (pending : phase.Pending)
    (n : Nat) (out : List Core.Admin) :
    ¬ Core.LabelExit n [] (Core.vals (stack.map Value.toCore) ++ site.coreCode selector phase ++ rest) out :=
  Proofs.Core.lookup_stays pending n out

open Wasm.Lime1.Execution in
theorem lime_lookup_stays {H : Type} {s : Store H} {site : Site} {caller : Frame}
    {selector : BitVec 32} {stack : List Value} {rest : List Admin} (n : Nat) (out : List Admin) :
    ¬ PureStep caller.module.types [.label n [] (limeSource s caller site selector stack rest).code] out :=
  Proofs.Lime1.lookup_stays n out

open Wasm.Lime1.Execution in
theorem lime_invoke_stays {H : Type} {s : Store H} {addr : Runtime.FuncAddr} {caller : Frame}
    {stack : List Value} {rest : List Admin} (n : Nat) (out : List Admin) :
    ¬ PureStep caller.module.types [.label n [] (limeResolved s caller stack rest (.resolved addr)).code] out :=
  Proofs.Lime1.invoke_stays n out

/-- Each adjacent pair is exactly one native step, with arbitrary preserved
numeric operands and pending instructions. Stops at a pending successful
call or the first trap, including any pending lowered Core instructions. -/
theorem core_trace_exact {H : Type} {P : Numerics.Profile} {s : Core.Store H}
    {caller : Frame} {site : Site} {program : Program} {selector : BitVec 32}
    {stack : List Value} {rest : List Core.Admin} {out : Outcome} {addr : Nat}
    (checked : site.check program caller = true) (allocated : program.CoreAllocated s)
    (tableFound : s.table? caller.toCore tableIndex = some (addr, site.table.toCore))
    (resolved : site.resolve program selector = some out) :
    out.coreTrace.IsChain (fun a b => ∀ dst,
      Core.Step P noHost (coreConfig s caller site selector stack rest a) dst ↔
        dst = coreConfig s caller site selector stack rest b) :=
  Proofs.Core.trace_exact checked allocated tableFound resolved

theorem core_trace_reachable {H : Type} {P : Numerics.Profile} {s : Core.Store H}
    {caller : Frame} {site : Site} {selector : BitVec 32}
    {stack : List Value} {rest : List Core.Admin} {out : Outcome}
    (exactSteps : out.coreTrace.IsChain (fun a b => ∀ dst,
      Core.Step P noHost (coreConfig s caller site selector stack rest a) dst ↔
        dst = coreConfig s caller site selector stack rest b))
    {phase : Phase} (member : phase ∈ out.coreTrace) :
    Core.Steps P noHost (coreConfig s caller site selector stack rest .start)
      (coreConfig s caller site selector stack rest phase) :=
  Proofs.Core.trace_reachable exactSteps member

theorem lime_step_iff {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame}
    {site : Site} {program : Program} {selector : BitVec 32} {stack : List Value}
    {rest : List Wasm.Lime1.Execution.Admin} {out : Outcome} {dst : Wasm.Lime1.Execution.Config H}
    (checked : site.check program caller = true) (allocated : program.LimeAllocated s)
    (tableFound : Wasm.Lime1.Execution.frameTable s caller = some site.table)
    (resolved : site.resolve program selector = some out) :
    Wasm.Lime1.Execution.Step CallFrame.limeNoHost (limeSource s caller site selector stack rest) dst ↔
      dst = limeResolved s caller stack rest out :=
  Proofs.Lime1.step_iff checked allocated tableFound resolved

/-- A successful resolution enters the allocated graph function on exactly its
ordered argument suffix. The caller prefix and continuation stay in place. -/
theorem core_enter_iff {H : Type} {P : Numerics.Profile} {s : Core.Store H}
    {caller : Frame} {site : Site} {program : Program} {selector : BitVec 32}
    {addr : Execution.Runtime.FuncAddr} {fn : Function}
    {saved args : List Value} {rest : List Core.Admin} {dst : Core.Config H}
    (allocated : program.CoreAllocated s) (found : program.lookup addr = some fn)
    (resolved : site.resolve program selector = some (.resolved addr))
    (typed : args.map Value.type = site.signature.params) :
    Core.Step P noHost (coreConfig s caller site selector (saved ++ args) rest (.call (some addr))) dst ↔
      dst = coreEntered s caller fn saved args rest :=
  Proofs.Core.enter_iff allocated found resolved typed

theorem lime_enter_iff {H : Type} {s : Wasm.Lime1.Execution.Store H}
    {caller : Frame} {site : Site} {program : Program} {selector : BitVec 32}
    {addr : Execution.Runtime.FuncAddr} {fn : Function}
    {saved args : List Value} {rest : List Wasm.Lime1.Execution.Admin} {dst : Wasm.Lime1.Execution.Config H}
    (allocated : program.LimeAllocated s) (found : program.lookup addr = some fn)
    (resolved : site.resolve program selector = some (.resolved addr))
    (typed : args.map Value.type = site.signature.params) :
    Wasm.Lime1.Execution.Step CallFrame.limeNoHost
      (limeResolved s caller (saved ++ args) rest (.resolved addr)) dst ↔
      dst = limeEntered s caller fn saved args rest :=
  Proofs.Lime1.enter_iff allocated found resolved typed

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect
