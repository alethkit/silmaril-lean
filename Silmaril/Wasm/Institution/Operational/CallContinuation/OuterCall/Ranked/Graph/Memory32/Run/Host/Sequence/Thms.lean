module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Host.Sequence.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.HostSequence

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.HostEntry.Sequence

open Execution.Runtime (Frame MemAddr MemInst Result Value)
open Wasm.V1.Execution

variable {H : Type} {seq : Sequence H} {host : HostSemantics H} {mode : MemoryMode}
  {program : Program} {memory : MemAddr} {calls : CallMode} {base : Store H} {initial : MemInst}
  {start : ByteArray} {outer : Frame} {args : List Value}

/-- A contracted return restores the live store and the checked continuation.
A value result feeds the next segment. A trap retains the returned bytes
through cleanup of the remaining code. -/
theorem return_ready (checked : seq.Checked mode program memory calls base outer args)
    (layout : Layout program base memory initial) (contract : seq.Contract host mode memory initial base)
    {bytes : ByteArray} {saved actual : List Value} {site : HostCall.V1.Site H}
    {later : List (HostSegment H)} {after : Store H} {r : Execution.Runtime.Result}
    (ready : seq.Ready mode program memory calls initial (.pending bytes saved actual site later))
    (returned : host site.target (storeWithBytes base memory initial bytes) actual (.returned after r)) :
    ∃ next, after = storeWithBytes base memory initial next ∧ bytes.size ≤ next.size ∧ HostCall.V1.ResultTyped site.signature.results r ∧
      Layout program after memory { initial with data := next } ∧
      seq.Ready mode program memory calls initial (seq.delivered outer args next saved later r) :=
  Proofs.return_ready checked layout contract ready returned

/-- The typed continuation and live-store invariant is preserved by each edge. -/
theorem Edge.ready (graphChecked : program.checkV1 memory mode calls = true)
    (checked : seq.Checked mode program memory calls base outer args)
    (layout : Layout program base memory initial) (extent : mode.extent initial.data.size start)
    (contract : seq.Contract host mode memory initial base) {src dst : Phase H}
    (edge : seq.Edge host mode program memory base initial start outer args src dst)
    (ready : seq.Ready mode program memory calls initial src) :
    seq.Ready mode program memory calls initial dst :=
  Proofs.preserves graphChecked checked layout extent contract edge ready

/-- Exact successors preserve native resolution, delivery and cleanup steps
for every reached site. -/
theorem v1_step_iff (graphChecked : program.checkV1 memory mode calls = true)
    (checked : seq.Checked mode program memory calls base outer args)
    (layout : Layout program base memory initial) (matched : mode.matches initial)
    (extent : mode.extent initial.data.size start) (contract : seq.Contract host mode memory initial base)
    {src : Phase H} (ready : seq.Ready mode program memory calls initial src) {dst : Config H} :
    Step host (seq.render base memory initial start outer args src) dst ↔
      ∃ next, seq.Edge host mode program memory base initial start outer args src next ∧
        seq.Ready mode program memory calls initial next ∧ dst = seq.render base memory initial start outer args next :=
  Proofs.step_iff graphChecked checked layout matched extent contract ready

/-- A reached trap can discard pending code and rejoin the host-free graph. -/
theorem trapped_run {bytes : ByteArray} {saved : List Value} {tail : List Admin} {dst : Phase H}
    (run : seq.Runs host mode program memory base initial start outer args (.trapped bytes saved tail) dst) :
    (∃ saved rest, dst = .trapped bytes saved rest) ∨ ∃ state, dst = .graph state :=
  Proofs.trapped_run run

/-- Finite endpoint correspondence through any number of source sites. -/
theorem v1_run_iff (graphChecked : program.checkV1 memory mode calls = true)
    (checked : seq.Checked mode program memory calls base outer args)
    (layout : Layout program base memory initial) (matched : mode.matches initial)
    (extent : mode.extent initial.data.size start) (contract : seq.Contract host mode memory initial base)
    {src : Phase H} (ready : seq.Ready mode program memory calls initial src) {dst : Config H} :
    Steps host (seq.render base memory initial start outer args src) dst ↔
      ∃ next, seq.Runs host mode program memory base initial start outer args src next ∧
        seq.Ready mode program memory calls initial next ∧ dst = seq.render base memory initial start outer args next :=
  Proofs.run_iff graphChecked checked layout matched extent contract ready

/-- The checked sequence starts at the ordinary source call. No entered frame
or pending callout is supplied. -/
theorem v1_call_run_iff (graphChecked : program.checkV1 memory mode calls = true)
    (checked : seq.Checked mode program memory calls base outer args)
    (layout : Layout program base memory initial) (matched : mode.matches initial)
    (extent : mode.extent initial.data.size start) (contract : seq.Contract host mode memory initial base)
    {dst : Config H} :
    Steps host ⟨storeWithBytes base memory initial start, outer, values args ++ [.source (.call seq.root.index)]⟩ dst ↔
      ∃ next, seq.Runs host mode program memory base initial start outer args .call next ∧
        seq.Ready mode program memory calls initial next ∧ dst = seq.render base memory initial start outer args next :=
  v1_run_iff (src := .call) graphChecked checked layout matched extent contract trivial

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.HostEntry.Sequence
