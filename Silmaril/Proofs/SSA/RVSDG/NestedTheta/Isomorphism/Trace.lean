module

public import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Defs
public import Silmaril.SSA.RVSDG.Petri.Defs
public import Silmaril.Proofs.SSA.RVSDG.Isomorphism.Addresses

@[expose] public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Proofs

open RVSDG.Isomorphism.Proofs (colours colours_get prefix_get site_length)
open RVSDG.Petri (collect)

universe u v w

variable {Ty : Type u} {F : Ty → Type w}

-- A slot represents failure for a whole vertex, even when it has no result ports.
def Slots (F : Ty → Type w) : List (Ports Ty) → Type (max u w)
  | [] => PUnit
  | head :: tail => Option (Tuple F head) × Slots F tail

def Slots.get {past : List (Ports Ty)} (slots : Slots F past) (i : Fin past.length) :
    Option (Tuple F past[i]) :=
  match past with
  | [] => i.elim0
  | _ :: _ => Fin.cases (motive := fun j => Option (Tuple F _[j])) slots.1 (fun j => slots.2.get j) i

def Slots.snoc {past : List (Ports Ty)} {head : Ports Ty}
    (slots : Slots F past) (value : Option (Tuple F head)) : Slots F (past ++ [head]) :=
  match past with
  | [] => (value, PUnit.unit)
  | _ :: _ => (slots.1, slots.2.snoc value)

def Slots.ofLocals {past : List (Ports Ty)} (values : Locals F past) : Slots F past :=
  match past with
  | [] => PUnit.unit
  | _ :: _ => (some values.1, ofLocals values.2)

theorem Slots.ofLocals_snoc {past : List (Ports Ty)} {head : Ports Ty}
    (values : Locals F past) (value : Tuple F head) :
    ofLocals (values.snoc value) = (ofLocals values).snoc (some value) := by
  induction past with
  | nil => rfl
  | cons head tail ih => exact congrArg (some values.1, ·) (ih values.2)

theorem Slots.ofLocals_get {past : List (Ports Ty)} (values : Locals F past) (i : Fin past.length) :
    (ofLocals values).get i = some (values.get i) := by
  induction past with
  | nil => exact i.elim0
  | cons head tail ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact ih values.2 j

def colour {args : Ports Ty} {past : List (Ports Ty)}
    (entry : Tuple F args) (slots : Slots F past) {t : Ty} :
    Origin args past t → Option (F t)
  | .arg p => some (entry.get p)
  | .output i p => (slots.get i).map (fun tuple => tuple.get p)

def read {args users : Ports Ty} {past : List (Ports Ty)} (wires : Wires args past users)
    (entry : Tuple F args) (slots : Slots F past) : Option (Tuple F users) :=
  collect (wires.map fun _ => colour entry slots)

theorem read_ofLocals {args users : Ports Ty} {past : List (Ports Ty)} (wires : Wires args past users)
    (entry : Tuple F args) (values : Locals F past) :
    read wires entry (Slots.ofLocals values) = some (wires.read entry values) := by
  induction wires with
  | nil => rfl
  | cons origin tail ih =>
    unfold read at ih
    simp only [read, Tuple.map, collect, ih, Wires.read]
    cases origin with
    | arg p => rfl
    | output i p => simp only [colour, Slots.ofLocals_get, Option.map_some]

-- Numeric projections retain both whole-vertex success and each port's type.
def store {past : List (Ports Ty)} : Slots F past → List (Option (List (Sigma F))) :=
  match past with
  | [] => fun _ => []
  | _ :: _ => fun slots => slots.1.map colours :: store slots.2

theorem store_length {past : List (Ports Ty)} (slots : Slots F past) :
    (store slots).length = past.length := by
  induction past with
  | nil => rfl
  | cons head tail ih => exact congrArg Nat.succ (ih slots.2)

theorem store_snoc {past : List (Ports Ty)} {head : Ports Ty} (slots : Slots F past)
    (value : Option (Tuple F head)) :
    store (slots.snoc value) = store slots ++ [value.map colours] := by
  induction past with
  | nil => rfl
  | cons head tail ih => exact congrArg (slots.1.map colours :: ·) (ih slots.2)

theorem store_get {past : List (Ports Ty)} (slots : Slots F past) (i : Fin past.length) :
    (store slots)[i.val]? = some ((slots.get i).map colours) := by
  induction past with
  | nil => exact i.elim0
  | cons head tail ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact ih slots.2 j

def lookup (entry : List (Sigma F)) (all : List (Option (List (Sigma F)))) : Address → Option (Sigma F)
  | .arg p => entry[p]?
  | .output i p => all[i]?.join.bind (·[p]?)

private theorem collect_colours {ts : Ports Ty} (tuple : Tuple (fun t => Option (F t)) ts) :
    (collect tuple).map colours =
      (colours tuple).mapM (fun ⟨t, value⟩ => value.map (Sigma.mk t)) := by
  induction tuple with
  | nil => simp [collect, colours, List.mapM_nil]
  | cons value tail ih =>
    simp only [colours, List.mapM_cons]
    rw [← ih]
    cases value <;> cases eq : collect tail <;> simp [collect, colours, eq]

private theorem read_sources {args users : Ports Ty} {past : List (Ports Ty)}
    (wires : Wires args past users) (entry : Tuple F args) (slots : Slots F past)
    (all : List (Option (List (Sigma F)))) (pref : store slots <+: all) :
    (colours (wires.map fun _ => colour entry slots)).map
        (fun ⟨t, value⟩ => value.map (Sigma.mk t)) =
      wires.addresses.map (lookup (colours entry) all) := by
  induction wires with
  | nil => rfl
  | cons origin tail ih =>
    simp only [Tuple.map, Wires.addresses, colours, List.map_cons, ih]
    congr 1
    cases origin with
    | arg p => exact (colours_get entry p).symm
    | output i p =>
      have bound : i.val < (store slots).length := by rw [store_length]; exact i.isLt
      simp only [colour, Origin.address, lookup, prefix_get pref bound, store_get, Option.join]
      cases eq : slots.get i with
      | none => rfl
      | some tuple => exact (colours_get tuple p).symm

private theorem sequence {α : Type (max u w)} (xs : List α) (f : α → Option (Sigma F)) :
    xs.mapM f = (xs.map f).mapM id := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.mapM_cons, List.map_cons, id, ih]

theorem read_colours {args users : Ports Ty} {past : List (Ports Ty)}
    (wires : Wires args past users) (entry : Tuple F args) (slots : Slots F past)
    (all : List (Option (List (Sigma F)))) (pref : store slots <+: all) :
    (read wires entry slots).map colours = (wires.addresses.map (lookup (colours entry) all)).mapM id := by
  simp only [read, collect_colours]
  rw [sequence (colours (wires.map fun _ => colour entry slots)), read_sources wires entry slots all pref]

theorem compare_reads {args args' ins ins' : Ports Ty} {past past' : List (Ports Ty)}
    (left : Wires args past ins) (right : Wires args' past' ins')
    (entry : Tuple F args) (entry' : Tuple F args') (inputs : colours entry = colours entry')
    (slots : Slots F past) (slots' : Slots F past')
    {all all' : List (Option (List (Sigma F)))} (pref : store slots <+: all) (pref' : store slots' <+: all')
    (rename : Nat → Nat) (wires : left.addresses.map (Address.rename rename) = right.addresses)
    (sources : ∀ i p, Address.output i p ∈ left.addresses → all[i]? = all'[rename i]?) :
    (read left entry slots).map colours = (read right entry' slots').map colours := by
  rw [read_colours left entry slots all pref, read_colours right entry' slots' all' pref']
  congr 1
  have observations : left.addresses.map (lookup (colours entry) all) =
      right.addresses.map (lookup (colours entry') all') := by
    rw [← wires, List.map_map]
    apply List.map_congr_left
    intro addr present
    cases addr with
    | arg p => exact congrArg (fun xs : List (Sigma F) => xs[p]?) inputs
    | output i p =>
      exact congrArg (fun slot : Option (Option (List (Sigma F))) =>
        slot.join.bind (fun xs => xs[p]?)) (sources i p present)
  exact observations

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

abbrev Erased (F : Ty → Type w) := List (Option (List (Sigma F)))

def trace (m : Model.{u, v, w} Op) (fuel : Nat) (entry : Tuple m.Val args) :
    (past sigs : List (Ports (PortType V S))) → Slots m.Val past →
    (nodes : Nodes Op args past sigs) → Runners m nodes → Slots m.Val (extend past sigs)
  | _, [], slots, _, _ => slots
  | past, head :: tail, slots, nodes, children =>
    let node := nodes 0
    let output := read node.inputs entry slots >>= node.kind.eval m fuel (children 0)
    trace m fuel entry (past ++ [head]) tail (slots.snoc output)
      (fun i => nodes i.succ) (fun i => children i.succ)

theorem trace_prefix (m : Model.{u, v, w} Op) (fuel : Nat) (entry : Tuple m.Val args)
    (past sigs : List (Ports (PortType V S))) (slots : Slots m.Val past)
    (nodes : Nodes Op args past sigs) (children : Runners m nodes) :
    store slots <+: store (trace m fuel entry past sigs slots nodes children) := by
  induction sigs generalizing past with
  | nil => exact ⟨[], List.append_nil _⟩
  | cons head tail ih =>
    simp only [trace]
    apply List.IsPrefix.trans _ (ih _ _ _ _)
    exact ⟨_, (store_snoc _ _).symm⟩

theorem trace_at (m : Model.{u, v, w} Op) (fuel : Nat) (entry : Tuple m.Val args)
    (past sigs : List (Ports (PortType V S))) (slots : Slots m.Val past)
    (nodes : Nodes Op args past sigs) (children : Runners m nodes) (i : Fin sigs.length) :
    let all := store (trace m fuel entry past sigs slots nodes children)
    let node := nodes i
    ∃ before : Slots m.Val (site past sigs i).1,
      store before <+: all ∧
      all[(site past sigs i).1.length]? = some
        ((read node.inputs entry before >>= node.kind.eval m fuel (children i)).map colours) := by
  induction sigs generalizing past with
  | nil => exact i.elim0
  | cons head tail ih =>
    let first := read (nodes 0).inputs entry slots >>= (nodes 0).kind.eval m fuel (children 0)
    let next := slots.snoc first
    let later := trace m fuel entry (past ++ [head]) tail next
      (fun j => nodes j.succ) (fun j => children j.succ)
    have preserves : store next <+: store later := trace_prefix m fuel entry _ _ _ _ _
    refine Fin.cases ?_ (fun j => ?_) i
    · have addsFirst : store slots <+: store next := ⟨[first.map colours], (store_snoc slots first).symm⟩
      refine ⟨slots, addsFirst.trans preserves, ?_⟩
      change (store later)[past.length]? = some (first.map colours)
      have bound : past.length < (store next).length := by rw [store_length, List.length_append]; simp
      rw [prefix_get preserves bound, store_snoc,
        List.getElem?_append_right (by simp only [store_length, Nat.le_refl]), store_length, Nat.sub_self]
      rfl
    · exact ih (past ++ [head]) next _ _ j

def graphTrace (m : Model.{u, v, w} Op) (fuel : Nat) (graph : Graph Op args [] sigs outs)
    (entry : Tuple m.Val args) : Slots m.Val (extend [] sigs) :=
  trace m fuel entry [] sigs PUnit.unit graph.nodes (fun i j input => (graph.children i j).run m fuel input)

theorem graphTrace_at (m : Model.{u, v, w} Op) (fuel : Nat) (graph : Graph Op args [] sigs outs)
    (entry : Tuple m.Val args) (i : Fin sigs.length) :
    let all := store (graphTrace m fuel graph entry)
    let node := graph.nodes i
    ∃ before : Slots m.Val (site [] sigs i).1,
      store before <+: all ∧
      all[i.val]? = some ((read node.inputs entry before >>= node.kind.eval m fuel
        (fun arm input => (graph.children i arm).run m fuel input)).map colours) := by
  simpa only [graphTrace, site_length, List.length_nil, Nat.zero_add] using
    trace_at m fuel entry [] sigs PUnit.unit graph.nodes
      (fun i arm input => (graph.children i arm).run m fuel input) i

abbrev completed (all : Erased F) : Prop := all.all Option.isSome = true

private theorem slots_complete {past : List (Ports Ty)} (values : Locals F past) :
    completed (store (Slots.ofLocals values)) := by
  induction past with
  | nil => rfl
  | cons head tail ih =>
    change (some (colours values.1) :: store (Slots.ofLocals values.2)).all Option.isSome = true
    simpa only [List.all_cons, Option.isSome_some, Bool.true_and] using ih values.2

private def finish {args users : Ports Ty} {past : List (Ports Ty)} (results : Wires args past users)
    (entry : Tuple F args) (slots : Slots F past) : Option (Tuple F users) :=
  if completed (store slots) then read results entry slots else none

private theorem trace_result (m : Model.{u, v, w} Op) (fuel : Nat) (entry : Tuple m.Val args)
    (past sigs : List (Ports (PortType V S))) (values : Locals m.Val past)
    (nodes : Nodes Op args past sigs) (children : Runners m nodes)
    (results : Wires args (extend past sigs) outs) :
    evalTable m fuel entry past sigs values nodes children results =
      finish results entry (trace m fuel entry past sigs (Slots.ofLocals values) nodes children) := by
  induction sigs generalizing past with
  | nil =>
    let wires : Wires args past outs := results
    change some (wires.read entry values) =
      if completed (store (Slots.ofLocals values)) then read wires entry (Slots.ofLocals values) else none
    rw [ite_eq_left (slots_complete values), read_ofLocals wires entry values]
  | cons head tail ih =>
    let node : Node Op args past head := nodes 0
    let run := node.kind.eval m fuel (children 0)
    let rest (result : Tuple m.Val head) := evalTable m fuel entry (past ++ [head]) tail
      (values.snoc result) (fun i => nodes i.succ) (fun i => children i.succ) results
    let fill (output : Option (Tuple m.Val head)) := finish results entry
      (trace m fuel entry (past ++ [head]) tail ((Slots.ofLocals values).snoc output)
        (fun i => nodes i.succ) (fun i => children i.succ))
    change (run (node.inputs.read entry values) >>= rest) =
      fill (read node.inputs entry (Slots.ofLocals values) >>= run)
    rw [read_ofLocals node.inputs entry values]
    change (run (node.inputs.read entry values) >>= rest) = fill (run (node.inputs.read entry values))
    generalize run (node.inputs.read entry values) = first
    dsimp only [fill]
    cases first with
    | none =>
      have pref := trace_prefix m fuel entry (past ++ [head]) tail ((Slots.ofLocals values).snoc
        (none : Option (Tuple m.Val head))) (fun i => nodes i.succ) (fun i => children i.succ)
      have failed : none ∈ store (trace m fuel entry (past ++ [head]) tail
          ((Slots.ofLocals values).snoc none) (fun i => nodes i.succ) (fun i => children i.succ)) :=
        pref.sublist.subset (by simp [store_snoc])
      exact (ite_eq_right (fun done => Bool.noConfusion ((List.all_eq_true.mp done) none failed))).symm
    | some result =>
      rw [← Slots.ofLocals_snoc]
      exact ih _ _ _ _ _

theorem graphTrace_result (m : Model.{u, v, w} Op) (fuel : Nat)
    (graph : Graph Op args [] sigs outs) (entry : Tuple m.Val args) :
    graph.run m fuel entry =
      if completed (store (graphTrace m fuel graph entry))
      then read graph.results entry (graphTrace m fuel graph entry) else none := by
  cases graph with
  | region nodes children results => exact trace_result m fuel entry [] sigs PUnit.unit nodes _ results

end Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Proofs
