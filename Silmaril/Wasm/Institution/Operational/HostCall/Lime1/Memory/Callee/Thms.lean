module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Memory.Callee.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.Memory.Callee.Native
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.Memory.Callee.Preservation

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.MemoryCallee

open Execution.Runtime (Frame Value)
open Wasm.Lime1.Execution

variable {H : Type} {base : Store H} {mem : Memory32 base} {site : IndirectSite} {callee : MemoryTarget}
  {caller : Frame} {saved : List Value} {tail : List Admin} {bytes written : ByteArray} {phase next : Phase}
  {dst : Config H}

theorem ready_step (linked : site.MemoryLinked mem)
    (registered : site.memoryLookup callee.address = some callee.fn) (move : Edge mem site callee bytes phase written next)
    (ready : Ready mem site callee phase) : Ready mem site callee next :=
  Proofs.ready_step linked registered move ready

theorem live_step (move : Edge mem site callee bytes phase written next) (live : mem.Live bytes) : mem.Live written :=
  Proofs.live_step move live

/-- A callee step preserves the live extent guard and the full ordered
argument and result checks for the active callee and suspended callers.
Only successful stores and growth update the shared bytes. -/
theorem preserves (linked : site.MemoryLinked mem)
    (registered : site.memoryLookup callee.address = some callee.fn) (move : Edge mem site callee bytes phase written next)
    (ready : Ready mem site callee phase) (live : mem.Live bytes) : Ready mem site callee next ∧ mem.Live written :=
  ⟨Proofs.ready_step linked registered move ready, Proofs.live_step move live⟩

/-- Native callee steps can only advance the extent. Host returns are governed
by their separate embedding contract. -/
theorem extent_mono (move : Edge mem site callee bytes phase written next) : bytes.size ≤ written.size :=
  Proofs.extent_mono move

/-- Exact native steps of the reached callee in the caller's operand and
instruction context, including rank-decreasing direct and indirect children.
A nested lookup consumes the live selector and either leaves a pending
invocation or traps with the current bytes. Native label and frame exits are
distinct. A child's frame exit restores the checked suffix or exposes a trap
for cleanup. -/
theorem step_iff (linked : site.MemoryLinked mem)
    (registered : site.memoryLookup callee.address = some callee.fn) (allocated : callee.Allocated base)
    (ready : Ready mem site callee phase) (live : mem.Live bytes) (notDone : ∀ out, phase ≠ .done out) :
    Internal (config mem caller saved tail callee bytes phase) dst ↔
      ∃ written next, Edge mem site callee bytes phase written next ∧ dst = config mem caller saved tail callee written next :=
  Proofs.step_iff linked registered allocated ready live notDone

/-- The suspended caller cannot reach a host while this callee is live. -/
theorem absent (allocated : callee.Allocated base) (ready : Ready mem site callee phase)
    (notDone : ∀ out, phase ≠ .done out) :
    Execution.Runtime.decomposeFrom? coding (mem.store bytes) [] (values saved ++ render callee phase ++ tail) = none :=
  Proofs.absent allocated ready notDone

/-- The caller's surrounding label remains in place while the callee steps. -/
theorem stays (notDone : ∀ out, phase ≠ .done out)
    {types : List Wasm.Lime1.FuncType} {n : Nat} {cont : Wasm.Lime1.Expr} {out : List Admin} :
    ¬ PureStep types [.label n cont (values saved ++ render callee phase ++ tail)] out :=
  Proofs.stays notDone

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.MemoryCallee
