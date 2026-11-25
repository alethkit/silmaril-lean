module

public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Isomorphism.Defs
public import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Isomorphism.Trace

@[expose] public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Petri.Isomorphism.Proofs

open RVSDG.Petri (Tokens Vertex)
open NestedTheta.Isomorphism.Proofs (Slots store store_get store_length store_snoc)
open RVSDG.Isomorphism.Proofs (colours prefix_get site_length)

universe u v w z

variable {Ty : Type u} {F : Ty → Type w}
variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args ins outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

def published {ts : Ports Ty} {n : Nat} {C : Fin n → Type z} :
    Vertex (Tuple F ts) C → Option (Tuple F ts)
  | .done values => some values
  | .pending | .waiting _ _ => none

def portTokens {ts : Ports Ty} : Option (Tuple F ts) → Tuple (fun t => Option (F t)) ts
  | none => RVSDG.Petri.absent ts
  | some values => values.map fun _ => some

theorem portTokens_published {ts : Ports Ty} {n : Nat} {C : Fin n → Type z}
    (cell : Vertex (Tuple F ts) C) : portTokens (published cell) = cell.outputs := by
  cases cell <;> rfl

def tokens {past : List (Ports Ty)} (slots : Slots F past) : Tokens F past :=
  match past with
  | [] => PUnit.unit
  | _ :: _ => (portTokens slots.1, tokens slots.2)

theorem tokens_snoc {past : List (Ports Ty)} {head : Ports Ty} (slots : Slots F past)
    (output : Option (Tuple F head)) : tokens (slots.snoc output) = (tokens slots).snoc (portTokens output) := by
  induction past with
  | nil => rfl
  | cons head tail ih => exact congrArg (portTokens slots.1, ·) (ih slots.2)

private theorem tokens_get {past : List (Ports Ty)} (slots : Slots F past) (i : Fin past.length) :
    (tokens slots).get i = portTokens (slots.get i) := by
  induction past with
  | nil => exact i.elim0
  | cons head tail ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact ih slots.2 j

private theorem portTokens_get {ts : Ports Ty} {t : Ty} (values : Option (Tuple F ts)) (p : Port ts t) :
    (portTokens values).get p = values.map (fun xs => xs.get p) := by
  induction p with
  | head => cases values with | none => rfl | some xs => cases xs; rfl
  | tail p ih =>
    cases values with
    | none => exact ih none
    | some xs => cases xs with | cons _ rest => exact ih (some rest)

theorem read_slots {args ins : Ports Ty} {past : List (Ports Ty)} (wires : Wires args past ins)
    (entry : Tuple F args) (slots : Slots F past) :
    RVSDG.Petri.read wires entry (tokens slots) = NestedTheta.Isomorphism.Proofs.read wires entry slots := by
  unfold RVSDG.Petri.read NestedTheta.Isomorphism.Proofs.read
  congr 1
  congr 1
  funext t origin
  cases origin with
  | arg p => rfl
  | output i p =>
    unfold RVSDG.Petri.colour NestedTheta.Isomorphism.Proofs.colour
    exact (congrArg (fun tup => tup.get p) (tokens_get slots i)).trans (portTokens_get (slots.get i) p)

structure Table (Op : Dialect.{u, v} V S) (args : Ports (PortType V S))
    (past sigs : List (Ports (PortType V S))) (outs : Ports (PortType V S)) where
  nodes : Nodes Op args past sigs
  children : (i : Fin sigs.length) → Children (Term Op) (nodes i)
  results : Wires args (extend past sigs) outs

abbrev Table.term (table : Table Op args past sigs outs) :=
  Term.fromTable past sigs table.nodes table.children table.results

def Table.tail {head : Ports (PortType V S)} (table : Table Op args past (head :: sigs) outs) :
    Table Op args (past ++ [head]) sigs outs :=
  ⟨fun i => table.nodes i.succ, fun i => table.children i.succ, table.results⟩

abbrev Table.cell (m : Model.{u, v, w} Op) (table : Table Op args past sigs outs) (i : Fin sigs.length) :=
  LocalMarking m (table.nodes i) (table.children i)

abbrev Table.get (m : Model.{u, v, w} Op) (table : Table Op args past sigs outs)
    (marks : Marking m table.term) (i : Fin sigs.length) : table.cell m i :=
  markingAt m past sigs table.nodes table.children table.results marks i

def Table.ofCells (m : Model.{u, v, w} Op) :
    {past sigs : List (Ports (PortType V S))} → (table : Table Op args past sigs outs) →
    ((i : Fin sigs.length) → table.cell m i) → Marking m table.term
  | _, [], _, _ => PUnit.unit
  | _, _ :: _, table, cells => (cells 0, table.tail.ofCells m (fun j => cells j.succ))

theorem Table.get_ofCells (m : Model.{u, v, w} Op) (table : Table Op args past sigs outs)
    (cells : (i : Fin sigs.length) → table.cell m i) (i : Fin sigs.length) :
    table.get m (table.ofCells m cells) i = cells i := by
  induction sigs generalizing past with
  | nil => exact i.elim0
  | cons head tail ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact ih table.tail (fun k => cells k.succ) j

theorem Table.marking_eq (m : Model.{u, v, w} Op) (table : Table Op args past sigs outs)
    (before after : Marking m table.term) (cells : ∀ i, table.get m before i = table.get m after i) :
    before = after := by
  induction sigs generalizing past with
  | nil => cases before; cases after; rfl
  | cons head tail ih =>
    exact Prod.ext (cells 0) (ih table.tail before.2 after.2 (fun i => cells i.succ))

theorem Table.unique_of_cells (m : Model.{u, v, w} Op) (table : Table Op args past sigs outs)
    (property : (i : Fin sigs.length) → table.cell m i → Prop)
    (selected : ∀ i, ∃! cell, property i cell) :
    ∃! marking : Marking m table.term, ∀ i, property i (table.get m marking i) := by
  classical
  let cells (i : Fin sigs.length) := Classical.choose (selected i).exists
  have valid (i : Fin sigs.length) : property i (cells i) := Classical.choose_spec (selected i).exists
  refine ⟨table.ofCells m cells, ?_, ?_⟩
  · intro i
    rw [table.get_ofCells]
    exact valid i
  · intro other pointwise
    apply table.marking_eq
    intro i
    rw [table.get_ofCells]
    exact (selected i).unique (pointwise i) (valid i)

def Table.set (m : Model.{u, v, w} Op) :
    {past sigs : List (Ports (PortType V S))} → (table : Table Op args past sigs outs) →
    Marking m table.term → (i : Fin sigs.length) → table.cell m i → Marking m table.term
  | _, [], _, _, i, _ => i.elim0
  | _, _ :: _, table, marks, i, cell =>
    Fin.cases (motive := fun j => table.cell m j → Marking m table.term)
      (fun cell => (cell, marks.2)) (fun j cell => (marks.1, table.tail.set m marks.2 j cell)) i cell

theorem Table.get_set_self (m : Model.{u, v, w} Op) (table : Table Op args past sigs outs)
    (marks : Marking m table.term) (i : Fin sigs.length) (cell : table.cell m i) :
    table.get m (table.set m marks i cell) i = cell := by
  induction sigs generalizing past with
  | nil => exact i.elim0
  | cons head tail ih =>
    revert cell
    refine Fin.cases ?_ (fun j => ?_) i
    · exact fun _ => rfl
    · exact fun cell => ih table.tail marks.2 j cell

theorem Table.get_set_other (m : Model.{u, v, w} Op) (table : Table Op args past sigs outs)
    (marks : Marking m table.term) (i j : Fin sigs.length) (cell : table.cell m i) (ne : j ≠ i) :
    table.get m (table.set m marks i cell) j = table.get m marks j := by
  induction sigs generalizing past with
  | nil => exact i.elim0
  | cons head tail ih =>
    revert cell ne
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · exact fun _ ne => False.elim (ne rfl)
      · exact fun _ _ => rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · exact fun _ _ => rfl
      · intro cell ne
        exact ih table.tail marks.2 i j cell (fun eq => ne (congrArg Fin.succ eq))

theorem Table.get_pending (m : Model.{u, v, w} Op) (table : Table Op args past sigs outs)
    (i : Fin sigs.length) : table.get m (pending m table.term) i = .pending := by
  induction sigs generalizing past with
  | nil => exact i.elim0
  | cons head tail ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact ih table.tail j

def Table.prefix (m : Model.{u, v, w} Op) :
    {past sigs : List (Ports (PortType V S))} → (table : Table Op args past sigs outs) →
    Marking m table.term → Slots m.Val past → (i : Fin sigs.length) → Slots m.Val (site past sigs i).1
  | _, [], _, _, _, i => i.elim0
  | past, head :: tail, table, marks, slots, i =>
    Fin.cases (motive := fun j => Slots m.Val (site past (head :: tail) j).1)
      slots (fun j => table.tail.prefix m marks.2 (slots.snoc (published marks.1)) j) i

def Table.outputs (m : Model.{u, v, w} Op) :
    {past sigs : List (Ports (PortType V S))} → (table : Table Op args past sigs outs) →
    Marking m table.term → Slots m.Val past → Slots m.Val (extend past sigs)
  | _, [], _, _, slots => slots
  | _, _ :: _, table, marks, slots => table.tail.outputs m marks.2 (slots.snoc (published marks.1))

theorem Table.outputs_prefix (m : Model.{u, v, w} Op) (table : Table Op args past sigs outs)
    (marks : Marking m table.term) (slots : Slots m.Val past) :
    store slots <+: store (table.outputs m marks slots) := by
  induction sigs generalizing past with
  | nil => exact ⟨[], List.append_nil _⟩
  | cons head tail ih =>
    change store slots <+: store (table.tail.outputs m marks.2 (slots.snoc (published marks.1)))
    exact List.IsPrefix.trans ⟨_, (store_snoc slots _).symm⟩ (ih table.tail marks.2 _)

theorem Table.prefix_outputs (m : Model.{u, v, w} Op) (table : Table Op args past sigs outs)
    (marks : Marking m table.term) (slots : Slots m.Val past) (i : Fin sigs.length) :
    store (table.prefix m marks slots i) <+: store (table.outputs m marks slots) := by
  induction sigs generalizing past with
  | nil => exact i.elim0
  | cons head tail ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact table.outputs_prefix m marks slots
    · exact ih table.tail marks.2 _ j

theorem Table.output_at (m : Model.{u, v, w} Op) (table : Table Op args past sigs outs)
    (marks : Marking m table.term) (slots : Slots m.Val past) (i : Fin sigs.length) :
    (store (table.outputs m marks slots))[past.length + i.val]? =
      some ((published (table.get m marks i)).map colours) := by
  induction sigs generalizing past with
  | nil => exact i.elim0
  | cons head tail ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · let next := slots.snoc (published marks.1)
      have pref := table.tail.outputs_prefix m marks.2 next
      have bound : past.length < (store next).length := by simp [store_length, next]
      change (store (table.tail.outputs m marks.2 next))[past.length]? =
        some ((published marks.1).map colours)
      rw [prefix_get pref bound]
      unfold next
      rw [store_snoc, List.getElem?_append_right (by simp only [store_length, Nat.le_refl]),
        store_length, Nat.sub_self]
      rfl
    · have idx : past.length + (Fin.succ j).val = (past ++ [head]).length + j.val := by
        simp only [Fin.val_succ, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [idx]
      exact ih table.tail marks.2 _ j

end Silmaril.SSA.RVSDG.NestedTheta.Petri.Isomorphism.Proofs
