module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Table

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Proofs

open Execution.Runtime (FuncAddr)
open StraightLine
open DirectSequence.Enclosing.Framed

private theorem target_mem (site : Sequence.Site) (i : site.TargetId) :
    leafTarget (site.target i) ∈ site.targets.map leafTarget :=
  List.mem_map_of_mem (List.getElem_mem i.isLt)

private theorem leaf_nesting {table : Table} {site : Sequence.Site} (owner : FuncAddr)
    (edges : ∀ i : site.TargetId, table.Resolved owner (site.target i).address) (q : Sequence.State site) :
    table.Nesting (owner :: leafFrames q) := by
  cases q with
  | active i q rest => cases q <;> simp [leafFrames, edges]
  | running | trapped => simp [leafFrames]

theorem nesting_of_check {table : Table} {call : Source.Invocation}
    (check : table.checkInvocation call = true) (q : Source.State call) :
    table.Nesting (frames q) := by
  simp only [Table.checkInvocation, Bool.and_eq_true] at check
  obtain ⟨checked, ⟨root, inner⟩, _⟩ := check
  have rootEntry := (checkEntry_iff ..).mp root
  have innerEntry := (checkEntry_iff ..).mp inner
  have innerEdge : table.Resolved call.target.address call.body.invocation.site.address :=
    resolved_of_target checked rootEntry (List.mem_cons_self ..)
  have innerLeaves (i : call.body.invocation.site.body.TargetId) :
      table.Resolved call.body.invocation.site.address (call.body.invocation.site.body.target i).address :=
    resolved_of_target checked innerEntry (target_mem _ i)
  have suffixLeaves (i : call.context.sequence.TargetId) :
      table.Resolved call.target.address (call.context.sequence.target i).address :=
    resolved_of_target checked rootEntry (List.mem_cons_of_mem _ (target_mem _ i))
  cases q with
  | call | invoke => simp [frames]
  | framed phase =>
    cases phase with
    | exit | done => simp [frames]
    | label body =>
      cases body with
      | continuation phase => exact leaf_nesting _ suffixLeaves phase
      | active phase =>
        cases phase with
        | label body => exact List.isChain_cons_cons.mpr ⟨innerEdge, leaf_nesting _ innerLeaves body⟩
        | exit => simp [frames, innerEdge]
        | call | invoke | done => simp [frames]

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Proofs
