module

public import Silmaril.SSA.PEG.Simple.Revert.Automatic.Defs
public import Silmaril.SSA.PEG.Simple.Revert.Thms
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Init.Data.Vector.OfFn

public section

namespace Silmaril.SSA.PEG.Simple.Revert.Automatic.Proofs

open RVSDG (Tuple)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params : List (Ty Data)} {result t : Ty Data} {n : Nat}
variable {g : Graph P params [result] n 0}

private theorem all_mem (rank : Fin n → Nat) (i : Fin n) : i ∈ order rank := by
  simp [order]

private theorem order_sorted (rank : Fin n → Nat) :
    (order rank).Pairwise (fun a b => rank b ≤ rank a) := by
  simpa [order] using
    (List.pairwise_mergeSort (le := fun (a b : Fin n) => decide (rank b ≤ rank a))
      (by simpa using fun (a b c : Fin n) h₁ h₂ => Nat.le_trans h₂ h₁)
      (by intro a b; simpa using Nat.le_total (rank b) (rank a)) (List.finRange n))

private theorem slot_lt {rank : Fin n → Nat}
    (accepted : DemandRank.check [.phase rank] g = true) (i : Fin n)
    (slot : Fin (g.node i).inputs.length) : rank ((g.node i).arg slot).id < rank i := by
  have ok := List.all_eq_true.mp (List.all_eq_true.mp accepted _ (List.mem_finRange i))
    slot (List.mem_finRange slot)
  by_contra h
  by_cases eq : rank ((g.node i).arg slot).id = rank i <;>
    simp [DemandRank.checkEdge, RankComponent.change, h, eq] at ok

private theorem edge_lt {rank : Fin n → Nat}
    (accepted : DemandRank.check [.phase rank] g = true) {i j : Fin n}
    (hj : j ∈ strictInputs g i) : rank j < rank i := by
  obtain ⟨slot, _, rfl⟩ := List.mem_map.mp hj
  exact slot_lt accepted i slot

private def OperandOrder (inputs : Fin n → List (Fin n)) : List (Fin n) → Prop
  | [] => True
  | i :: rows => (∀ j ∈ inputs i, j ∈ rows) ∧ OperandOrder inputs rows

private theorem operands_ordered {rank : Fin n → Nat} {inputs : Fin n → List (Fin n)}
    (decreases : ∀ i j, j ∈ inputs i → rank j < rank i) (rows : List (Fin n))
    (sorted : rows.Pairwise (fun a b => rank b ≤ rank a))
    (closed : ∀ i ∈ rows, ∀ j, rank j < rank i → j ∈ rows) :
    OperandOrder inputs rows := by
  induction rows with
  | nil => trivial
  | cons i rows ih =>
    obtain ⟨ge, tail⟩ := List.pairwise_cons.mp sorted
    have remove {j : Fin n} (h : rank j < rank i) (mem : j ∈ i :: rows) : j ∈ rows := by
      rcases List.mem_cons.mp mem with rfl | hr
      · exact False.elim (Nat.lt_irrefl _ h)
      · exact hr
    refine ⟨fun j hj => remove (decreases i j hj) (closed i (by simp) j (decreases i j hj)),
      ih tail ?_⟩
    intro a ha b lt
    exact remove (Nat.lt_of_lt_of_le lt (ge a ha)) (closed a (by simp [ha]) b lt)

private theorem heights_succ (g : Graph P params [result] n 0) (k : Nat) (i : Fin n) :
    (heights g (k + 1))[i.val] =
      (operands g i).foldl (fun h j => max h ((heights g k)[j.val] + 1)) 0 := by
  simp [heights, Nat.repeat, heightStep]

private theorem foldHeights_congr {rows : List (Fin n)} {a b : Fin n → Nat}
    (same : ∀ i ∈ rows, a i = b i) (init : Nat) :
    rows.foldl (fun h i => max h (a i + 1)) init =
      rows.foldl (fun h i => max h (b i + 1)) init := by
  induction rows generalizing init with
  | nil => rfl
  | cons i rows ih =>
    simp only [List.foldl_cons, same i (by simp)]
    exact ih (fun j hj => same j (List.mem_cons_of_mem _ hj)) _

private theorem heights_stable {rows : List (Fin n)} (ordered : OperandOrder (operands g) rows)
    (i : Fin n) (hi : i ∈ rows) (k : Nat) (enough : rows.length ≤ k) :
    (heights g (k + 1))[i.val] = (heights g k)[i.val] := by
  induction rows generalizing i k with
  | nil => simp at hi
  | cons a rows ih =>
    obtain ⟨earlier, tail⟩ := ordered
    rcases List.mem_cons.mp hi with rfl | hi
    · cases k with
      | zero => simp at enough
      | succ k =>
        rw [heights_succ g (k + 1), heights_succ g k]
        apply foldHeights_congr
        intro j hj
        exact ih tail j (earlier j hj) k (Nat.le_of_succ_le_succ enough)
    · exact ih tail i hi k (by simpa using Nat.le_trans (Nat.le_succ rows.length) enough)

private theorem foldHeight_le {rows : List (Fin n)} (fn : Fin n → Nat) (start : Nat) :
    start ≤ rows.foldl (fun h i => max h (fn i + 1)) start := by
  induction rows generalizing start with
  | nil => exact Nat.le_refl _
  | cons i rows ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

private theorem operandHeight_le {rows : List (Fin n)} {i : Fin n} (mem : i ∈ rows)
    (fn : Fin n → Nat) (start : Nat) :
    fn i + 1 ≤ rows.foldl (fun h j => max h (fn j + 1)) start := by
  induction rows generalizing start with
  | nil => simp at mem
  | cons a rows ih =>
    rcases List.mem_cons.mp mem with rfl | mem
    · exact Nat.le_trans (Nat.le_max_right _ _) (foldHeight_le fn _)
    · exact ih mem _

theorem infer_rank (g : Graph P params [result] n 0) {rank : Fin n → Nat}
    (valid : DemandRank.check [.phase rank] g = true) :
    DemandRank.check [.phase (inferRank g)] g = true := by
  let rows := order rank
  have edges := operands_ordered (inputs := operands g) (fun i j mem => by
    obtain ⟨slot, _, rfl⟩ := List.mem_map.mp mem
    exact slot_lt valid i slot) rows (order_sorted rank) (fun _ _ j _ => all_mem rank j)
  have length : rows.length = n := by simp [rows, order]
  apply List.all_eq_true.mpr
  intro i _
  apply List.all_eq_true.mpr
  intro slot _
  have mem : ((g.node i).arg slot).id ∈ operands g i :=
    List.mem_map.mpr ⟨slot, List.mem_finRange slot, rfl⟩
  have lt : inferRank g ((g.node i).arg slot).id < inferRank g i := by
    have saved := heights_stable edges i (all_mem rank i) n length.le
    rw [heights_succ] at saved
    change (heights g n)[((g.node i).arg slot).id.val] < (heights g n)[i.val]
    rw [← saved]
    exact operandHeight_le mem (fun j => (heights g n)[j.val]) 0
  simp [DemandRank.checkEdge, RankComponent.change, lt]

private theorem selected_sublist (rows needed : List (Fin n)) :
    List.Sublist (demandedRows g rows needed) rows := by
  induction rows generalizing needed with
  | nil => exact .slnil
  | cons i rows ih =>
    simp only [demandedRows]
    split
    · exact .cons_cons i (ih _)
    · exact .cons i (ih _)

private theorem initial_selected {rows needed : List (Fin n)} {j : Fin n}
    (hr : j ∈ rows) (hn : j ∈ needed) : j ∈ demandedRows g rows needed := by
  induction rows generalizing needed with
  | nil => simp at hr
  | cons i rows ih =>
    simp only [demandedRows]
    by_cases hi : i ∈ needed
    · rw [ite_eq_left hi]
      rcases List.mem_cons.mp hr with rfl | hr
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hr (List.mem_append_right _ hn))
    · rw [ite_eq_right hi]
      rcases List.mem_cons.mp hr with rfl | hr
      · exact False.elim (hi hn)
      · exact ih hr hn

private theorem selected_ordered {rows : List (Fin n)} (h : OperandOrder (strictInputs g) rows)
    (needed : List (Fin n)) : OperandOrder (strictInputs g) (demandedRows g rows needed) := by
  induction rows generalizing needed with
  | nil => trivial
  | cons i rows ih =>
    obtain ⟨here, rest⟩ := h
    simp only [demandedRows]
    split
    · exact ⟨fun j hj => initial_selected (here j hj) (List.mem_append_left _ hj), ih rest _⟩
    · exact ih rest _

private def Ready (g : Graph P params [result] n 0) : List (Fin n) → List (Fin n) → Prop
  | [], _ => True
  | i :: rows, live => (∀ j ∈ strictInputs g i, j ∈ live) ∧ Ready g rows (i :: live)

private theorem ready_snoc {rows live : List (Fin n)} (h : Ready g rows live) (i : Fin n)
    (last : ∀ j ∈ strictInputs g i, j ∈ rows ++ live) :
    Ready g (rows ++ [i]) live := by
  induction rows generalizing live with
  | nil => exact ⟨last, trivial⟩
  | cons a rows ih =>
    refine ⟨h.1, ih h.2 (fun j hj => ?_)⟩
    have mem := last j hj
    simp only [List.cons_append, List.mem_cons, List.mem_append] at mem ⊢
    rcases mem with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

private theorem ready_reverse {rows : List (Fin n)} (h : OperandOrder (strictInputs g) rows)
    (live : List (Fin n)) : Ready g rows.reverse live := by
  induction rows with
  | nil => trivial
  | cons i rows ih =>
    rw [List.reverse_cons]
    exact ready_snoc (ih h.2) i (fun j hj =>
      List.mem_append_left _ (List.mem_reverse.mpr (h.1 j hj)))

private theorem findSlot_complete {live : List (Fin n)} {i : Fin n} (h : i ∈ live) :
    ∃ p, findSlot i live = some p := by
  induction live with
  | nil => simp at h
  | cons a live ih =>
    by_cases eq : a = i
    · subst a
      exact ⟨.head, by simp [findSlot]⟩
    · have mem : i ∈ live := (List.mem_cons.mp h).resolve_left (Ne.symm eq)
      obtain ⟨p, hp⟩ := ih mem
      exact ⟨.tail p, by simp [findSlot, eq, hp]⟩

private theorem reads_complete {sort : Fin n → Ty Data} {live : List (Fin n)}
    {ts : List (Ty Data)} (refs : Tuple (Ref sort) ts)
    (h : ∀ slot : Fin ts.length, (refs.get (portAt ts slot)).id ∈ live) :
    ∃ reads, Reads.check refs = some (reads : Reads sort live refs) := by
  induction refs with
  | nil => exact ⟨.nil, rfl⟩
  | cons r rs ih =>
    have head : r.id ∈ live := h 0
    obtain ⟨p, hp⟩ := findSlot_complete head
    obtain ⟨ps, hps⟩ := ih (fun s => h s.succ)
    exact ⟨.cons p ps, by simp [Reads.check, hp, hps]⟩

private def bindOnly : List (Fin n) → Plan n
  | [] => .done
  | i :: rows => .bind i (bindOnly rows)

private theorem emit_straight (straight : StraightLine g)
    (armPlan : List (Fin n) → Fin n → Nat → Option (Plan n × Nat))
    (rows live : List (Fin n)) (budget : Nat) (room : rows.length ≤ budget) :
    emitBindings g armPlan rows live budget = some (bindOnly rows, budget - rows.length) := by
  induction rows generalizing live budget with
  | nil => rfl
  | cons i rows ih =>
    cases budget with
    | zero => simp at room
    | succ budget =>
      simp [emitBindings, straight i, ih _ _ (Nat.le_of_succ_le_succ room), bindOnly]

private theorem basicRow {sort : Fin n → Ty Data} {out : Ty Data}
    (row : Node P params (Fin 0) sort out) :
    (∃ p, row = Node.ofLabel (.param p) .nil) ∨
      (∃ (ins : List (Ty Data)) (op : P ins out) (refs : Tuple (Ref sort) ins), row = Node.ofLabel (.op op) refs) ∨
      (∃ refs, row = Node.ofLabel .phi refs) := by
  rcases row with ⟨ins, label, refs⟩
  cases label with
  | param p =>
    cases refs
    exact Or.inl ⟨p, rfl⟩
  | op op => exact Or.inr (Or.inl ⟨_, op, refs, rfl⟩)
  | phi => exact Or.inr (Or.inr ⟨refs, rfl⟩)
  | theta l | eval l | pass l => exact l.elim0

private theorem checkBinding_congr {root : Ref g.sort t} {live needed : List (Fin n)}
    {i : Fin n} (h : i ∈ needed) {a b : Node P params (Fin 0) g.sort (g.sort i)}
    (ha : g.node i = a) (eq : a = b) (next : Option (Schedule g root (i :: live) needed)) :
    Schedule.checkBinding i h a ha next = Schedule.checkBinding i h b (ha.trans eq) next := by
  cases eq
  rfl

private theorem check_bindings (straight : StraightLine g) (root : Ref g.sort t)
    (rows live needed : List (Fin n)) (ready : Ready g rows live)
    (demanded : ∀ i ∈ rows, i ∈ needed) (target : root.id ∈ rows ++ live) :
    ∃ s, (bindOnly rows).check g root live needed = some s ∧ s.bindings = rows := by
  induction rows generalizing live with
  | nil =>
    have avail : root.id ∈ live := target
    obtain ⟨p, hp⟩ := findSlot_complete avail
    exact ⟨.done p, by simp [bindOnly, Plan.check, hp], rfl⟩
  | cons i rows ih =>
    have hi := demanded i (by simp)
    have ht : root.id ∈ rows ++ i :: live := by
      simp only [List.cons_append, List.mem_cons, List.mem_append] at target ⊢
      rcases target with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    obtain ⟨tail, htail, sites⟩ := ih _ ready.2 (fun j hj => demanded j (by simp [hj])) ht
    rcases basicRow (g.node i) with ⟨p, row⟩ | ⟨ins, instr, refs, row⟩ | ⟨refs, row⟩
    · refine ⟨.param i hi p row tail, ?_, by simp [Schedule.bindings, sites]⟩
      simp only [bindOnly, Plan.check, dite_eq_left hi, htail, checkBinding_congr hi rfl row]
      rfl
    · have available (slot : Fin ins.length) :
          (refs.get (portAt ins slot)).id ∈ live := by
        apply ready.1
        have inputs := congrArg (fun (node : Node P params (Fin 0) g.sort (g.sort i)) =>
          (strictSlots node.label).map (fun s => (node.arg s).id)) row
        change strictInputs g i = (List.finRange ins.length).map
          (fun s => (refs.get (portAt ins s)).id) at inputs
        rw [inputs]
        exact List.mem_map.mpr ⟨slot, List.mem_finRange slot, rfl⟩
      obtain ⟨reads, hr⟩ := reads_complete refs available
      refine ⟨.op i hi instr refs row reads tail, ?_, by simp [Schedule.bindings, sites]⟩
      simp only [bindOnly, Plan.check, dite_eq_left hi, htail, checkBinding_congr hi rfl row]
      change (match Reads.check refs with
        | none => none
        | some checked => some (Schedule.op i hi instr refs row checked tail)) = _
      rw [hr]
    · have h := straight i
      unfold arms at h
      rw [row] at h
      cases h

private theorem check_reveals (root : Ref g.sort t) (rows live needed : List (Fin n))
    (body : Plan n) (sites : List (Fin n))
    (bodyOk : ∀ needed', (∀ i ∈ demandedRows g rows needed ++ needed, i ∈ needed') →
      ∃ s, body.check g root live needed' = some s ∧ s.bindings = sites) :
    ∃ s, (emitReveals (demandedRows g rows needed) body).check g root live needed = some s ∧
      s.bindings = sites := by
  induction rows generalizing needed with
  | nil => exact bodyOk needed (fun _ h => h)
  | cons i rows ih =>
    by_cases hi : i ∈ needed
    · simp only [demandedRows, ite_eq_left hi] at bodyOk ⊢
      obtain ⟨s, hs, hsites⟩ := ih (strictInputs g i ++ needed) (fun needed' incl =>
        bodyOk needed' (fun j hj => incl j (by
          simp only [List.cons_append, List.mem_cons, List.mem_append] at hj ⊢
          rcases hj with rfl | h | h
          · exact Or.inr (Or.inr hi)
          · exact Or.inl h
          · exact Or.inr (Or.inr h))))
      exact ⟨.reveal i hi s, by simp [emitReveals, Plan.check, hi, hs], hsites⟩
    · simp only [demandedRows, ite_eq_right hi] at bodyOk ⊢
      exact ih needed bodyOk

theorem check_straight (g : Graph P params [result] n 0) (rank : Fin n → Nat)
    (straight : StraightLine g) (ordered : DemandRank.check [.phase rank] g = true) :
    (checkRanked g rank).isSome = true := by
  let root := returnRef g
  let rows := order rank
  let selected := demandedRows g rows [root.id]
  have edges := operands_ordered (fun _ _ => edge_lt ordered) rows (order_sorted rank) (fun _ _ j _ => all_mem rank j)
  have sub : List.Sublist selected rows := selected_sublist rows _
  have length : rows.length = n := by simp [rows, order]
  have room : selected.reverse.length ≤ n := by simpa [List.length_reverse, length] using sub.length_le
  have nodup : selected.reverse.Nodup := List.nodup_reverse.mpr
    (sub.nodup ((List.mergeSort_perm _ _).nodup_iff.mpr (List.nodup_finRange n)))
  have target : root.id ∈ selected.reverse ++ [] :=
    List.mem_append_left _ (List.mem_reverse.mpr (initial_selected (all_mem rank root.id) (by simp)))
  have ready := ready_reverse (selected_ordered edges [root.id]) []
  obtain ⟨cert, parsed, sites⟩ := check_reveals root rows [] [root.id] (bindOnly selected.reverse)
    selected.reverse (fun needed incl =>
      check_bindings straight root _ _ _ ready
        (fun i hi => incl i (List.mem_append_left _ (List.mem_reverse.mp hi))) target)
  have planned : plan g rank = some (emitReveals selected (bindOnly selected.reverse)) := by
    have filter : (rows.filter fun i => i ∉ ([] : List (Fin n))) = rows := by simp
    simp only [plan, planScope]
    change (Option.map Prod.fst (do
      let (body, left) ← emitBindings g (planScope g rows n)
        (demandedRows g (rows.filter fun i => i ∉ ([] : List (Fin n))) [root.id]).reverse [] n
      return (emitReveals (demandedRows g (rows.filter fun i => i ∉ ([] : List (Fin n))) [root.id])
        body, left))) = _
    rw [filter]
    change (Option.map Prod.fst (do
      let (body, left) ← emitBindings g (planScope g rows n) selected.reverse [] n
      return (emitReveals selected body, left))) = _
    rw [emit_straight straight _ _ _ _ room]
    rfl
  change (Plan.check g (emitReveals selected (bindOnly selected.reverse)) (returnRef g)
    [] [(returnRef g).id]) = some cert at parsed
  simp [checkRanked, ordered, planned, Certificate.check, parsed, sites, nodup]

end Silmaril.SSA.PEG.Simple.Revert.Automatic.Proofs
