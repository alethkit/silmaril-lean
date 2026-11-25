module

public import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Petri.Isomorphism.Table

@[expose] public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Petri.Isomorphism.Proofs

open NestedTheta.Isomorphism.Proofs (Slots store store_snoc completed)
open RVSDG.Isomorphism.Proofs (colours)
open RVSDG.Petri (Tokens)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args ins outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

abbrev Body (kind : Kind Op ins outs) (cs : Fin kind.arity → List (Ports (PortType V S))) :=
  (arm : Fin kind.arity) → Term Op kind.entry [] (cs arm) kind.exit

/-- The action at one vertex. A step in a selected child remains a single step. -/
inductive LocalFire (m : Model.{u, v, w} Op) (kind : Kind Op ins outs)
    {cs : Fin kind.arity → List (Ports (PortType V S))} (bodies : Body kind cs)
    (input : Option (Tuple m.Val ins)) :
    Local m ⟨ins, outs, kind⟩ (fun j => Marking m (bodies j)) →
    Local m ⟨ins, outs, kind⟩ (fun j => Marking m (bodies j)) → Prop where
  | primitive {args : Tuple m.Val ins} {output : Tuple m.Val outs}
      (ready : input = some args) (computed : Petri.primitive m kind args = some output) :
      LocalFire m kind bodies input .pending (.done output)
  | enter {args : Tuple m.Val ins} {arm : Fin kind.arity} {received : Tuple m.Val kind.entry}
      (ready : input = some args) (guard : activate m kind args = some (arm, received)) :
      LocalFire m kind bodies input .pending (.waiting arm (received, pending m (bodies arm)))
  | advance {arm : Fin kind.arity} {received : Tuple m.Val kind.entry}
      {before after : Marking m (bodies arm)}
      (step : Fire m (past := []) (bodies arm) received PUnit.unit before after) :
      LocalFire m kind bodies input (.waiting arm (received, before)) (.waiting arm (received, after))
  | commit {arm : Fin kind.arity} {received : Tuple m.Val kind.entry} {child : Marking m (bodies arm)}
      {output : Tuple m.Val outs} {returned : Tuple m.Val kind.exit}
      (ready : finished m (past := []) (bodies arm) received PUnit.unit child = some returned)
      (choice : route m kind arm returned = .inl output) :
      LocalFire m kind bodies input (.waiting arm (received, child)) (.done output)
  | restart {arm : Fin kind.arity} {received next : Tuple m.Val kind.entry}
      {child : Marking m (bodies arm)} {returned : Tuple m.Val kind.exit} {feedback : Tuple m.Val ins}
      (ready : finished m (past := []) (bodies arm) received PUnit.unit child = some returned)
      (choice : route m kind arm returned = .inr feedback)
      (guard : activate m kind feedback = some (arm, next)) :
      LocalFire m kind bodies input (.waiting arm (received, child))
        (.waiting arm (next, pending m (bodies arm)))

def Table.readAt (m : Model.{u, v, w} Op) (table : Table Op args past sigs outs)
    (entry : Tuple m.Val args) (slots : Slots m.Val past) (marks : Marking m table.term)
    (i : Fin sigs.length) : Option (Tuple m.Val (table.nodes i).ins) :=
  RVSDG.Petri.read (table.nodes i).inputs entry (tokens (table.prefix m marks slots i))

abbrev Table.At (m : Model.{u, v, w} Op) (table : Table Op args past sigs outs)
    (entry : Tuple m.Val args) (slots : Slots m.Val past) (marks : Marking m table.term)
    (i : Fin sigs.length) (next : table.cell m i) :=
  LocalFire m (table.nodes i).kind (table.children i) (table.readAt m entry slots marks i)
    (table.get m marks i) next

theorem Table.localize (m : Model.{u, v, w} Op) (table : Table Op args past sigs outs)
    (entry : Tuple m.Val args) (slots : Slots m.Val past) (before after : Marking m table.term)
    (step : Fire m table.term entry (tokens slots) before after) :
    ∃ (i : Fin sigs.length) (next : table.cell m i),
      table.At m entry slots before i next ∧ after = table.set m before i next := by
  induction sigs generalizing past with
  | nil =>
    change Fire m (.ret table.results) entry (tokens slots) before after at step
    cases step
  | cons head tail ih =>
    change Fire m (.bind (table.nodes 0) (table.children 0) table.tail.term)
      entry (tokens slots) before after at step
    cases step with
    | primitive ready result => exact ⟨0, _, .primitive ready result, rfl⟩
    | enter ready guard => exact ⟨0, _, .enter ready guard, rfl⟩
    | advance step => exact ⟨0, _, .advance step, rfl⟩
    | commit ready decision => exact ⟨0, _, .commit ready decision, rfl⟩
    | restart ready decision guard => exact ⟨0, _, .restart ready decision guard, rfl⟩
    | @later _ _ _ _ _ _ _ _ _ _ vertex old new later =>
      let nextSlots : Slots m.Val (past ++ [head]) := slots.snoc (published vertex)
      have step : Fire m table.tail.term entry (tokens nextSlots) old new := by
        rw [show tokens nextSlots = (tokens slots).snoc vertex.outputs from
          (tokens_snoc slots _).trans (congrArg (tokens slots).snoc (portTokens_published vertex))]
        exact later
      obtain ⟨i, next, fires, updated⟩ := ih table.tail nextSlots old new step
      exact ⟨i.succ, next, fires, congrArg (vertex, ·) updated⟩

theorem Table.fire_set (m : Model.{u, v, w} Op) (table : Table Op args past sigs outs)
    (entry : Tuple m.Val args) (slots : Slots m.Val past) (before : Marking m table.term)
    (i : Fin sigs.length) (next : table.cell m i) (step : table.At m entry slots before i next) :
    Fire m table.term entry (tokens slots) before (table.set m before i next) := by
  induction sigs generalizing past with
  | nil => exact i.elim0
  | cons head tail ih =>
    revert next step
    refine Fin.cases ?_ (fun j => ?_) i
    · intro next step
      obtain ⟨old, rest⟩ := before
      change LocalFire m (table.nodes 0).kind (table.children 0)
        (RVSDG.Petri.read (table.nodes 0).inputs entry (tokens slots)) old next at step
      cases step with
      | primitive ready result => exact .primitive ready result
      | enter ready guard => exact .enter ready guard
      | advance step => exact .advance step
      | commit ready decision => exact .commit ready decision
      | restart ready decision guard => exact .restart ready decision guard
    · intro next step
      let nextSlots := slots.snoc (published before.1)
      have moved := ih table.tail nextSlots before.2 j next step
      rw [show tokens nextSlots = (tokens slots).snoc before.1.outputs from
        (tokens_snoc slots _).trans (congrArg (tokens slots).snoc (portTokens_published before.1))] at moved
      exact .later moved

theorem Table.finished_outputs (m : Model.{u, v, w} Op) (table : Table Op args past sigs outs)
    (entry : Tuple m.Val args) (slots : Slots m.Val past) (marks : Marking m table.term)
    (initially : completed (store slots)) :
    finished m table.term entry (tokens slots) marks =
      if completed (store (table.outputs m marks slots)) then
        NestedTheta.Isomorphism.Proofs.read table.results entry (table.outputs m marks slots)
      else none := by
  induction sigs generalizing past with
  | nil =>
    let results : Wires args past outs := table.results
    change RVSDG.Petri.read results entry (tokens slots) =
      if completed (store slots) then NestedTheta.Isomorphism.Proofs.read results entry slots else none
    rw [ite_eq_left initially, read_slots]
  | cons head tail ih =>
    obtain ⟨cell, rest⟩ := marks
    let next := slots.snoc (published cell)
    let all := table.tail.outputs m rest next
    have pref := table.tail.outputs_prefix m rest next
    change finished m (.bind (table.nodes 0) (table.children 0) table.tail.term)
      entry (tokens slots) (cell, rest) = if completed (store all) then _ else none
    have blocked (missing : published cell = none) : ¬ completed (store all) := by
      intro done
      have absent : none ∈ store next := by simp [next, store_snoc, missing]
      exact Bool.noConfusion ((List.all_eq_true.mp done) none (pref.sublist.subset absent))
    cases cell with
    | pending => exact (ite_eq_right (blocked rfl)).symm
    | waiting arm child => exact (ite_eq_right (blocked rfl)).symm
    | done output =>
      have filled : completed (store next) := by
        rw [show store next = store slots ++ [some (colours output)] from
          store_snoc slots (some output)]
        simp only [completed, List.all_append, initially, List.all_cons, Option.isSome_some,
          List.all_nil, Bool.and_self]
      have result := ih table.tail next rest filled
      have eq : tokens next = (tokens slots).snoc (output.map fun _ => some) := tokens_snoc slots (some output)
      rw [eq] at result
      exact result

end Silmaril.SSA.RVSDG.NestedTheta.Petri.Isomorphism.Proofs
