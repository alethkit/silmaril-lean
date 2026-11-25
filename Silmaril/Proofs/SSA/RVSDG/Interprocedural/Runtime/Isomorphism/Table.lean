module

public import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Values

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Proofs

open RVSDG.Isomorphism.Proofs (colours prefix_get source_before site_length extend_length)
open NestedTheta.Isomorphism.Proofs
  (Slots store store_length store_snoc read read_ofLocals completed Erased)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {ids : GlobalRel}
variable {args args' outs outs' : Ports (Ty V S)}
variable {past sigs sigs' : List (Ports (Ty V S))}

/-- The local computation at a vertex, with typed operands supplied by its wiring. -/
structure Row (m : Machine.{u, v, w} Op) (args : Ports (Ty V S))
    (past : List (Ports (Ty V S))) (outs : Ports (Ty V S)) where
  ins : Ports (Ty V S)
  wires : Wires args past ins
  run : Tuple m.Val ins → Option (Tuple m.Val outs)

abbrev Rows (m : Machine.{u, v, w} Op) (args : Ports (Ty V S))
    (past sigs : List (Ports (Ty V S))) :=
  (i : Fin sigs.length) → Row m args (site past sigs i).1 (site past sigs i).2

def runRows (entry : Tuple m.Val args) :
    (past sigs : List (Ports (Ty V S))) → Locals m.Val past → Rows m args past sigs →
    Wires args (extend past sigs) outs → Option (Tuple m.Val outs)
  | _, [], values, _, results => some (results.read entry values)
  | past, head :: tail, values, rows, results => do
    let row := rows 0
    let output ← row.run (row.wires.read entry values)
    runRows entry (past ++ [head]) tail (values.snoc output) (fun i => rows i.succ) results

private def trace (entry : Tuple m.Val args) :
    (past sigs : List (Ports (Ty V S))) → Slots m.Val past → Rows m args past sigs →
    Slots m.Val (extend past sigs)
  | _, [], slots, _ => slots
  | past, head :: tail, slots, rows =>
    let row := rows 0
    let output := (read row.wires entry slots).bind row.run
    trace entry (past ++ [head]) tail (slots.snoc output) (fun i => rows i.succ)

/-- The typed store just before a designated row, including absent outputs. -/
def beforeAt (entry : Tuple m.Val args) :
    (past sigs : List (Ports (Ty V S))) → Slots m.Val past → Rows m args past sigs →
    (i : Fin sigs.length) → Slots m.Val (site past sigs i).1
  | _, [], _, _, i => i.elim0
  | past, head :: tail, slots, rows, i =>
    let row := rows 0
    let output := (read row.wires entry slots).bind row.run
    Fin.cases (motive := fun j => Slots m.Val (site past (head :: tail) j).1) slots
      (fun j => beforeAt entry (past ++ [head]) tail (slots.snoc output) (fun k => rows k.succ) j) i

/-- Observe the typed operands of a row before running it. -/
def readRowInput (entry : Tuple m.Val args) (values : Locals m.Val past)
    (rows : Rows m args past sigs) (i : Fin sigs.length) : Option (Tuple m.Val (rows i).ins) :=
  read (rows i).wires entry (beforeAt entry past sigs (Slots.ofLocals values) rows i)

theorem readRowInput_zero (entry : Tuple m.Val args) (values : Locals m.Val past)
    {head : Ports (Ty V S)} (rows : Rows m args past (head :: sigs)) :
    readRowInput entry values rows 0 = some ((rows 0).wires.read entry values) :=
  read_ofLocals (rows 0).wires entry values

theorem readRowInput_succ (entry : Tuple m.Val args) (values : Locals m.Val past)
    {head : Ports (Ty V S)} (rows : Rows m args past (head :: sigs))
    (output : Tuple m.Val head) (first : (rows 0).run ((rows 0).wires.read entry values) = some output)
    (i : Fin sigs.length) :
    readRowInput entry values rows i.succ =
      readRowInput entry (values.snoc output) (fun j => rows j.succ) i := by
  change read (rows i.succ).wires entry
    (beforeAt entry (past ++ [head]) sigs
      ((Slots.ofLocals values).snoc ((read (rows 0).wires entry (Slots.ofLocals values)).bind (rows 0).run))
        (fun j => rows j.succ) i) = _
  erw [read_ofLocals, Option.bind_some, first, ← Slots.ofLocals_snoc]
  rfl

private theorem trace_prefix (entry : Tuple m.Val args) (slots : Slots m.Val past) (rows : Rows m args past sigs) :
    store slots <+: store (trace entry past sigs slots rows) := by
  induction sigs generalizing past with
  | nil => exact ⟨[], List.append_nil _⟩
  | cons head tail ih =>
    change store slots <+: store (trace entry (past ++ [head]) tail (slots.snoc _) (fun i => rows i.succ))
    exact List.IsPrefix.trans ⟨_, (store_snoc slots _).symm⟩ (ih _ _)

private theorem trace_at (entry : Tuple m.Val args) (slots : Slots m.Val past) (rows : Rows m args past sigs)
    (i : Fin sigs.length) :
    let all := store (trace entry past sigs slots rows)
    let row := rows i
    let before := beforeAt entry past sigs slots rows i
    store before <+: all ∧ all[(site past sigs i).1.length]? =
      some (((read row.wires entry before).bind row.run).map colours) := by
  induction sigs generalizing past with
  | nil => exact i.elim0
  | cons head tail ih =>
    let first := (read (rows 0).wires entry slots).bind (rows 0).run
    let next := slots.snoc first
    let later := trace entry (past ++ [head]) tail next (fun j => rows j.succ)
    have preserves : store next <+: store later := trace_prefix entry next _
    refine Fin.cases ?_ (fun j => ?_) i
    · have added : store slots <+: store next := ⟨[first.map colours], (store_snoc slots first).symm⟩
      refine ⟨added.trans preserves, ?_⟩
      change (store later)[past.length]? = some (first.map colours)
      have bound : past.length < (store next).length := by rw [store_length, List.length_append]; simp
      rw [prefix_get preserves bound, store_snoc,
        List.getElem?_append_right (by simp only [store_length, Nat.le_refl]), store_length, Nat.sub_self]
      rfl
    · exact ih next _ j

private theorem complete_locals (values : Locals m.Val past) : completed (store (Slots.ofLocals values)) := by
  induction past with
  | nil => rfl
  | cons head tail ih =>
    change (some (colours values.1) :: store (Slots.ofLocals values.2)).all Option.isSome = true
    simpa only [List.all_cons, Option.isSome_some, Bool.true_and] using ih values.2

private def finish (results : Wires args past outs) (entry : Tuple m.Val args) (slots : Slots m.Val past) :
    Option (Tuple m.Val outs) :=
  if completed (store slots) then read results entry slots else none

private theorem runRows_trace (entry : Tuple m.Val args) (values : Locals m.Val past)
    (rows : Rows m args past sigs) (results : Wires args (extend past sigs) outs) :
    runRows entry past sigs values rows results =
      finish results entry (trace entry past sigs (Slots.ofLocals values) rows) := by
  induction sigs generalizing past with
  | nil =>
    let wires : Wires args past outs := results
    change some (wires.read entry values) =
      if completed (store (Slots.ofLocals values)) then read wires entry (Slots.ofLocals values) else none
    rw [ite_eq_left (complete_locals values), read_ofLocals wires entry values]
  | cons head tail ih =>
    let row : Row m args past head := rows 0
    let rest (output : Tuple m.Val head) := runRows entry (past ++ [head]) tail
      (values.snoc output) (fun i => rows i.succ) results
    let finishWith (output : Option (Tuple m.Val head)) := finish results entry
      (trace entry (past ++ [head]) tail ((Slots.ofLocals values).snoc output) (fun i => rows i.succ))
    change (row.run (row.wires.read entry values)).bind rest =
      finishWith ((read row.wires entry (Slots.ofLocals values)).bind row.run)
    rw [read_ofLocals row.wires entry values, Option.bind_some]
    generalize row.run (row.wires.read entry values) = first
    dsimp only [finishWith]
    cases first with
    | none =>
      let slots := (Slots.ofLocals values).snoc (none : Option (Tuple m.Val head))
      have pref := trace_prefix entry slots (fun i => rows i.succ)
      have missing : none ∈ store (trace entry (past ++ [head]) tail slots (fun i => rows i.succ)) :=
        pref.sublist.subset (by simp [slots, store_snoc])
      exact (ite_eq_right (fun done => Bool.noConfusion ((List.all_eq_true.mp done) none missing))).symm
    | some output =>
      rw [← Slots.ofLocals_snoc]
      exact ih _ _ _

private theorem slot_presence {left right : Option (Option (List (Sigma m.Val)))}
    (pair : StoreSlot m ids left right) : left.join.isSome = right.join.isSome := by
  cases pair with
  | none => rfl
  | some rel => cases rel <;> rfl

private theorem complete_at {all : Erased m.Val} {n : Nat} (length : all.length = n) :
    completed all ↔ ∀ i : Fin n, (all[i.val]?.join).isSome = true := by
  subst n
  simp only [completed, List.all_eq_true]
  constructor
  · intro done i
    rw [List.getElem?_eq_getElem i.isLt, Option.join_some]
    exact done _ (List.getElem_mem _)
  · intro done item mem
    obtain ⟨i, bound, eq⟩ := List.mem_iff_getElem.mp mem
    have h := done ⟨i, bound⟩
    change (all[i]?.join).isSome = true at h
    rwa [List.getElem?_eq_getElem bound, Option.join_some, eq] at h

private theorem complete_related {allL allR : Erased m.Val} {n k : Nat}
    (lenL : allL.length = n) (lenR : allR.length = k) (rename : Fin n ≃ Fin k)
    (vertices : ∀ i : Fin n, StoreSlot m ids allL[i.val]? allR[(rename i).val]?) :
    completed allL ↔ completed allR := by
  rw [complete_at lenL, complete_at lenR]
  constructor
  · intro done j
    have eq := slot_presence (vertices (rename.symm j))
    rw [rename.apply_symm_apply] at eq
    exact eq.symm.trans (done (rename.symm j))
  · intro done i
    exact (slot_presence (vertices i)).trans (done (rename i))

private theorem trace_related (rename : Fin sigs.length ≃ Fin sigs'.length)
    (inL : Tuple m.Val args) (inR : Tuple m.Val args') (entry : TupleRelated m ids inL inR)
    (left : Rows m args [] sigs) (right : Rows m args' [] sigs')
    (operands : ∀ i, (left i).wires.addresses.map (Address.rename (renameVertex rename)) =
      (right (rename i)).wires.addresses)
    (steps : ∀ i x y, TupleRelated m ids x y →
      RunRelated m ids ((left i).run x) ((right (rename i)).run y))
    (i : Nat) (valid : i < sigs.length) :
    StoreSlot m ids (store (trace inL [] sigs PUnit.unit left))[i]?
      (store (trace inR [] sigs' PUnit.unit right))[renameVertex rename i]? := by
  let empty : Slots m.Val [] := PUnit.unit
  let slotsL := trace inL [] sigs empty left
  let slotsR := trace inR [] sigs' empty right
  let allL := store slotsL
  let allR := store slotsR
  induction i using Nat.strongRecOn with
  | ind i earlier =>
    let j : Fin sigs.length := ⟨i, valid⟩
    obtain ⟨prefL, valueL⟩ := trace_at inL empty left j
    obtain ⟨prefR, valueR⟩ := trace_at inR empty right (rename j)
    simp only [site_length, List.length_nil, Nat.zero_add] at valueL valueR
    simp only [renameVertex, dite_eq_left valid]
    change StoreSlot m ids allL[j.val]? allR[(rename j).val]?
    rw [valueL, valueR]
    apply Option.Rel.some
    apply tags_of_run
    apply bind_related _ (steps j)
    apply read_related _ _ inL inR entry _ _ prefL prefR _ (operands j)
    intro producer port mem
    have earlierProducer : producer < i := by
      simpa only [site_length, List.length_nil, Nat.zero_add, j] using source_before (left j).wires mem
    exact earlier producer earlierProducer (Nat.lt_trans earlierProducer valid)

/-- Match operands at a pair of corresponding rows with the same per-row
semantics. The store proof uses the actual producer edges. -/
theorem readRowInput_related (rename : Fin sigs.length ≃ Fin sigs'.length)
    (inL : Tuple m.Val args) (inR : Tuple m.Val args') (entry : TupleRelated m ids inL inR)
    (left : Rows m args [] sigs) (right : Rows m args' [] sigs')
    (operands : ∀ i, (left i).wires.addresses.map (Address.rename (renameVertex rename)) =
      (right (rename i)).wires.addresses)
    (steps : ∀ i x y, TupleRelated m ids x y →
      RunRelated m ids ((left i).run x) ((right (rename i)).run y)) (i : Fin sigs.length) :
    RunRelated m ids (readRowInput (past := []) inL PUnit.unit left i) (readRowInput (past := []) inR PUnit.unit right (rename i)) := by
  unfold readRowInput
  apply read_related _ _ inL inR entry _ _ (trace_at inL _ left i).1 (trace_at inR _ right (rename i)).1
    _ (operands i)
  intro producer port mem
  have earlier : producer < i.val := by
    simpa only [site_length, List.length_nil, Nat.zero_add] using source_before (left i).wires mem
  exact trace_related rename inL inR entry left right operands steps producer (Nat.lt_trans earlier i.isLt)

theorem runRows_related (rename : Fin sigs.length ≃ Fin sigs'.length)
    (inL : Tuple m.Val args) (inR : Tuple m.Val args') (entry : TupleRelated m ids inL inR)
    (left : Rows m args [] sigs) (right : Rows m args' [] sigs')
    (outputsL : Wires args (extend [] sigs) outs) (outputsR : Wires args' (extend [] sigs') outs')
    (operands : ∀ i, (left i).wires.addresses.map (Address.rename (renameVertex rename)) =
      (right (rename i)).wires.addresses)
    (results : outputsL.addresses.map (Address.rename (renameVertex rename)) = outputsR.addresses)
    (steps : ∀ i x y, TupleRelated m ids x y →
      RunRelated m ids ((left i).run x) ((right (rename i)).run y)) :
    RunRelated m ids (runRows inL [] sigs PUnit.unit left outputsL)
      (runRows inR [] sigs' PUnit.unit right outputsR) := by
  let empty : Slots m.Val [] := PUnit.unit
  let slotsL := trace inL [] sigs empty left
  let slotsR := trace inR [] sigs' empty right
  let allL := store slotsL
  let allR := store slotsR
  have paired := trace_related rename inL inR entry left right operands steps
  have lenL : allL.length = sigs.length := by simp [allL, slotsL, store_length, extend_length]
  have lenR : allR.length = sigs'.length := by simp [allR, slotsR, store_length, extend_length]
  have full := complete_related lenL lenR rename (fun i => by
    simpa only [renameVertex, dite_eq_left i.isLt] using paired i.val i.isLt)
  have leftTrace := runRows_trace inL (past := []) PUnit.unit left outputsL
  have rightTrace := runRows_trace inR (past := []) PUnit.unit right outputsR
  rw [leftTrace, rightTrace]
  change RunRelated m ids (finish outputsL inL slotsL) (finish outputsR inR slotsR)
  unfold finish
  by_cases done : completed allL
  · have doneR := full.mp done
    rw [ite_eq_left done, ite_eq_left doneR]
    refine read_related outputsL outputsR inL inR entry slotsL slotsR
      ⟨[], List.append_nil _⟩ ⟨[], List.append_nil _⟩ _ results ?_
    intro producer port mem
    apply paired
    simpa only [extend_length, List.length_nil, Nat.zero_add] using source_before outputsL mem
  · rw [ite_eq_right done, ite_eq_right (fun h => done (full.mpr h))]
    exact .none

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Proofs
