module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Proofs

open Execution.Runtime (FuncAddr)

private theorem lookup_mem {table : Table} {address : FuncAddr} {entry : Entry}
    (lookedUp : table.lookup address = some entry) : some entry ∈ table.entries := by
  cases found : table.entries[address.value]? with
  | none => simp [Table.lookup, found] at lookedUp
  | some slot =>
    have same : slot = some entry := by simpa [Table.lookup, found] using lookedUp
    exact same ▸ List.mem_of_getElem? found

theorem check_iff (table : Table) :
    table.check = true ↔
    ∀ entry, some entry ∈ table.entries → ∀ target ∈ entry.targets,
      ∃ callee, table.lookup target.address = some callee ∧
        entry.declaration.module.funcs[target.index.toNat]? = some target.address ∧
        callee.declaration = target.declaration ∧ callee.rank < entry.rank := by
  have one (entry : Entry) (target : CallTarget) : table.checkTarget entry target = true ↔
      ∃ callee, table.lookup target.address = some callee ∧
        entry.declaration.module.funcs[target.index.toNat]? = some target.address ∧
        callee.declaration = target.declaration ∧ callee.rank < entry.rank := by
    cases found : table.lookup target.address <;> simp [Table.checkTarget, found, and_assoc]
  constructor
  · intro check entry member target used
    exact (one entry target).mp (List.all_eq_true.mp (List.all_eq_true.mp check _ member) _ used)
  · intro valid
    apply List.all_eq_true.mpr
    intro slot member
    cases slot with
    | none => rfl
    | some entry =>
      exact List.all_eq_true.mpr fun target used => (one entry target).mpr (valid entry member target used)

theorem resolved_of_target {table : Table} (checked : table.check = true)
    {address : FuncAddr} {decl : Declaration} {targets : List CallTarget} {target : CallTarget}
    (source : table.Contains address decl targets) (used : target ∈ targets) :
    table.Resolved address target.address := by
  obtain ⟨rank, found⟩ := source
  obtain ⟨callee, lookup, resolves, declaration, _⟩ := (check_iff table).mp checked _ (lookup_mem found) target used
  exact ⟨⟨decl, rank, targets⟩, target, callee, found, used, rfl, resolves, lookup, declaration⟩

theorem rank_decreases {table : Table} (checked : table.check = true) {caller callee : FuncAddr}
    (edge : table.Resolved caller callee) : table.rank callee < table.rank caller := by
  obtain ⟨source, target, destination, found, used, rfl, _, lookup, _⟩ := edge
  obtain ⟨entry, same, _, _, lower⟩ := (check_iff table).mp checked _ (lookup_mem found) target used
  have eq := Option.some.inj (same.symm.trans lookup)
  subst destination
  simpa [Table.rank, same, found] using lower

theorem checkEntry_iff (table : Table) (address : FuncAddr) (decl : Declaration) (targets : List CallTarget) :
    table.checkEntry address decl targets = true ↔ table.Contains address decl targets := by
  cases found : table.lookup address with
  | none => simp [Table.checkEntry, Table.Contains, found]
  | some entry =>
    cases entry
    simp [Table.checkEntry, Table.Contains, found]

theorem wellFounded {table : Table} (checked : table.check = true) :
    WellFounded (fun callee caller => table.Resolved caller callee) :=
  Subrelation.wf (fun edge => rank_decreases checked edge) (measure table.rank).wf

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Proofs
