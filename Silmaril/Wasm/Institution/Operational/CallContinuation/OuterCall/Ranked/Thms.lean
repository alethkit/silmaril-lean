module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Table
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Body

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked

open Execution.Runtime (FuncAddr)
open DirectSequence.Enclosing.Framed

theorem Table.check_iff (table : Table) :
    table.check = true ↔
    ∀ entry, some entry ∈ table.entries → ∀ target ∈ entry.targets,
      ∃ callee, table.lookup target.address = some callee ∧
        entry.declaration.module.funcs[target.index.toNat]? = some target.address ∧
        callee.declaration = target.declaration ∧ callee.rank < entry.rank :=
  Proofs.check_iff table

theorem Table.resolved_of_target {table : Table} (checked : table.check = true)
    {address : FuncAddr} {decl : Declaration} {targets : List CallTarget} {target : CallTarget}
    (source : table.Contains address decl targets) (used : target ∈ targets) :
    table.Resolved address target.address :=
  Proofs.resolved_of_target checked source used

theorem Table.rank_decreases {table : Table} (checked : table.check = true) {caller callee : FuncAddr}
    (edge : table.Resolved caller callee) : table.rank callee < table.rank caller :=
  Proofs.rank_decreases checked edge

theorem Table.checkEntry_iff (table : Table) (address : FuncAddr) (decl : Declaration) (targets : List CallTarget) :
    table.checkEntry address decl targets = true ↔ table.Contains address decl targets :=
  Proofs.checkEntry_iff table address decl targets

theorem Table.wellFounded {table : Table} (checked : table.check = true) :
    WellFounded (fun callee caller => table.Resolved caller callee) :=
  Proofs.wellFounded checked

/-- Consecutive entered frames in the fragment are linked by resolved direct calls. -/
theorem Table.nesting_of_check {table : Table} {call : Source.Invocation}
    (check : table.checkInvocation call = true) (q : Source.State call) :
    table.Nesting (frames q) :=
  Proofs.nesting_of_check check q

theorem Table.ranks_of_check {table : Table} {call : Source.Invocation}
    (check : table.checkInvocation call = true) (q : Source.State call) :
    (frames q).IsChain (fun caller callee => table.rank callee < table.rank caller) := by
  have checked : table.check = true := (Bool.and_eq_true_iff.mp check).1
  exact (table.nesting_of_check check q).imp (fun _ _ edge => table.rank_decreases checked edge)

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked
