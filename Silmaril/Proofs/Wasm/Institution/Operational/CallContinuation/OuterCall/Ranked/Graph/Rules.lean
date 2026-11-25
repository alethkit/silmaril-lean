module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Proofs

open Execution.Runtime (FuncAddr Value)

theorem lookup_table (program : Program) (address : FuncAddr) :
    program.table.lookup address = (program.lookup address).map Function.entry := by
  unfold Table.lookup Program.table Program.lookup
  rw [List.getElem?_map]
  cases program.functions[address.value]? with
  | none => rfl
  | some slot => cases slot <;> rfl

theorem target_resolved {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} {target : CallTarget}
    (found : program.lookup address = some fn) (used : target ∈ fn.targets) :
    program.order target.address address :=
  Table.resolved_of_target (Program.rankCheck checked)
    ⟨fn.rank, by rw [lookup_table, found]; rfl⟩ used

theorem map_child {fn : Function} {r₁ r₂ : CallTarget → Phase → Phase → Prop} {a b : Phase}
    (map : ∀ target ∈ fn.targets, ∀ {c d}, r₁ target c d → r₂ target c d)
    (step : Layer fn r₁ a b) : Layer fn r₂ a b := by
  cases step with
  | resolve args => exact .resolve args
  | enter args typed => exact .enter args typed
  | numeric step => exact .numeric step
  | localSet write => exact .localSet write
  | localTee write => exact .localTee write
  | unreachable args stack rest => exact .unreachable args stack rest
  | dispatch locals saved operands target rest used count => exact .dispatch locals saved operands target rest used count
  | child locals saved target rest used live step => exact .child locals saved target rest used live (map target used step)
  | discard step => exact .discard step
  | returnLabel locals stack rest => exact .returnLabel locals stack rest
  | returnFrame locals extra results arity => exact .returnFrame locals extra results arity
  | leaveValues args stack => exact .leaveValues args stack
  | leaveTrap args => exact .leaveTrap args
  | leaveFrame args result typed => exact .leaveFrame args result typed

private theorem unfold_edge {program : Program} (checked : program.check = true) (address : FuncAddr) (a b : Phase) :
    program.Edge checked address a b ↔
      ∃ fn, program.lookup address = some fn ∧
        Layer fn (fun target c d => ∃ _ : program.order target.address address,
          program.Edge checked target.address c d) a b := by
  conv_lhs =>
    unfold Program.Edge
    rw [WellFounded.fix_eq]
  rfl

theorem edge_iff {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} {a b : Phase} (found : program.lookup address = some fn) :
    program.Edge checked address a b ↔
      Layer fn (fun target => program.Edge checked target.address) a b := by
  rw [unfold_edge checked]
  constructor
  · rintro ⟨current, lookup, step⟩
    have same := Option.some.inj (lookup.symm.trans found)
    subst current
    exact map_child (fun _ _ _ _ ⟨_, edge⟩ => edge) step
  · intro step
    exact ⟨fn, found, map_child (fun _ used _ _ edge => ⟨target_resolved checked found used, edge⟩) step⟩

theorem active_iff {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn)
    {target : CallTarget} (used : target ∈ fn.targets) {a : Phase} (live : a.Active)
    {locals saved : List Value} {rest : List Op} {b : Phase} :
    program.Edge checked address (.label locals (.active saved target a rest)) b ↔
      ∃ out, program.Edge checked target.address a out ∧ b = .label locals (Body.attach saved target rest out) := by
  rw [edge_iff checked found]
  constructor
  · intro step
    cases step with
    | child _ _ _ _ _ _ step => exact ⟨_, step, rfl⟩
  · rintro ⟨out, step, rfl⟩
    exact .child locals saved target rest used live step

private theorem source_active {program : Program} {checked : program.check = true}
    {address : FuncAddr} {a b : Phase} (ready : ∀ args, a ≠ .call args)
    (edge : program.Edge checked address a b) : a.Active := by
  obtain ⟨_, _, step⟩ := (unfold_edge checked address a b).mp edge
  cases step with
  | resolve args => exact (ready args rfl).elim
  | _ => trivial

theorem not_call {program : Program} {checked : program.check = true}
    {address : FuncAddr} {a b : Phase} (edge : program.Edge checked address a b) (args : List Value) :
    b ≠ .call args := by
  obtain ⟨_, _, step⟩ := (unfold_edge checked address a b).mp edge
  cases step <;> simp

theorem lift_child {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn)
    {target : CallTarget} (used : target ∈ fn.targets) {a b : Phase} (live : a.Active)
    {locals saved : List Value} {rest : List Op} (run : program.Runs checked target.address a b) :
    program.Runs checked address (.label locals (.active saved target a rest))
      (.label locals (Body.attach saved target rest b)) := by
  have noCall (operands : List Value) : a ≠ .call operands := by
    intro eq
    subst a
    exact live
  have first : Body.attach saved target rest a = .active saved target a rest := by
    cases a <;> simp_all [Body.attach, Phase.Active]
  rw [← first]
  induction run with
  | refl => exact .refl
  | @tail q r before step ih =>
    have notAtCall (operands : List Value) : q ≠ .call operands := by
      cases before with
      | refl => exact noCall operands
      | tail _ edge => exact not_call edge operands
    have active := source_active notAtCall step
    have attach : Body.attach saved target rest q = .active saved target q rest := by
      cases q <;> simp_all [Body.attach, Phase.Active]
    apply ih.tail
    rw [attach]
    exact (active_iff checked found used active).mpr ⟨r, step, rfl⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Proofs
