module
public import Silmaril.Formats.Sqlite.VirtualTable.Defs

public section
namespace Silmaril.Proofs.Formats.Sqlite.VirtualTable
open Silmaril.Formats.Sqlite.VirtualTable

theorem checkHonesty_iff {width : Nat} {query : Query width} {plan : Plan}
    {snapshot : Snapshot width} {rows : Relation width} :
    checkHonesty query plan snapshot rows = true ↔ Honest query plan snapshot rows := by
  simp only [checkHonesty, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨⟨⟨⟨⟨layout, members⟩, unique⟩, covers⟩, omits⟩, order⟩
    refine ⟨layout, members, unique, covers, omits, ?_⟩
    intro consumed dir requested
    simpa [consumed, requested] using order
  · intro honest
    refine ⟨⟨⟨⟨⟨honest.layout, honest.fromSnapshot⟩, honest.uniqueScan⟩, honest.covers⟩,
      honest.omits⟩, ?_⟩
    cases consumed : plan.orderByConsumed
    · simp
    · right
      have present : query.input.orderBy.isSome = true := by
        have := honest.layout
        simp [Plan.validLayout, consumed] at this
        exact this.2
      cases requested : query.input.orderBy with
      | none => simp [requested] at present
      | some dir => simpa [requested] using honest.order consumed dir requested

theorem scanRows_trace {width : Nat} {cursor : Cursor width} {rows : Relation width}
    (h : cursor.scanRows = .ok rows) : ScanTrace cursor rows := by
  cases cursor <;> simp [Cursor.scanRows] at h
  subst rows
  rename_i remaining
  induction remaining with
  | nil => exact .endOfScan
  | cons row rest ih => exact .step rfl rfl rfl ih

theorem trace_scanRows {width : Nat} {cursor : Cursor width} {rows : Relation width}
    (trace : ScanTrace cursor rows) : cursor.scanRows = .ok rows := by
  induction trace with
  | endOfScan => rfl
  | @step cursor next row rows _ read advance _ ih =>
    cases cursor with
    | unfiltered | failed | closed => simp [Cursor.current] at read
    | scanning remaining =>
      cases remaining with
      | nil => simp [Cursor.current] at read
      | cons actual rest =>
        simp [Cursor.current] at read
        simp [Cursor.xNext] at advance
        subst row
        subst next
        simp [Cursor.scanRows] at ih ⊢
        exact ih

private theorem matches_split {width : Nat} (query : Query width) (keep : Nat → Bool)
    (row : Row width) (h : query.matches keep row = true) :
    query.matches (fun i => !keep i) row = query.matches (fun _ => true) row := by
  apply Bool.eq_iff_iff.mpr
  simp only [Query.matches, List.all_eq_true] at h ⊢
  constructor
  · intro other
    rintro ⟨⟨term, rhs⟩, i⟩ mem
    cases chosen : keep i
    · simpa [chosen] using other _ mem
    · simpa [chosen] using h _ mem
  · intro all
    rintro ⟨⟨term, rhs⟩, i⟩ mem
    simp [show term.op.test (row.get term.column) rhs = true by simpa using all _ mem]

private theorem residual_perm {width : Nat} {query : Query width} {plan : Plan}
    {snapshot : Snapshot width} {rows : Relation width}
    (honest : Honest query plan snapshot rows) :
    (rows.filter (query.matches fun i => !plan.omits i)).Perm (query.matchingRows snapshot) := by
  have eq : rows.filter (query.matches fun i => !plan.omits i) =
      rows.filter (query.matches fun _ => true) :=
    List.filter_congr (fun row mem => matches_split query plan.omits row (honest.omits row mem))
  rw [eq]
  exact honest.covers

theorem finish_perm {width : Nat} {query : Query width} {plan : Plan}
    {snapshot : Snapshot width} {rows : Relation width}
    (honest : Honest query plan snapshot rows) :
    (query.finish plan rows).Perm (query.matchingRows snapshot) := by
  have residual := residual_perm honest
  unfold Query.finish
  split
  · split
    · exact residual
    · exact (List.mergeSort_perm ..).trans residual
  · exact residual

theorem direction_sorted {width : Nat} (dir : Direction) (rows : Relation width) :
    (dir.sort rows).Pairwise (fun a b => dir.before a b = true) := by
  apply List.pairwise_mergeSort
  · cases dir <;> simp only [Direction.before, decide_eq_true_eq]
    · exact fun _ _ _ hab hbc => Int64.le_trans hab hbc
    · exact fun _ _ _ hab hbc => Int64.le_trans hbc hab
  · cases dir <;> simp only [Direction.before, Bool.or_eq_true, decide_eq_true_eq]
    · exact fun a b => Int64.le_total a.rowid b.rowid
    · exact fun a b => Int64.le_total b.rowid a.rowid

private theorem Snapshot.eq_of_rowid {width : Nat} (snapshot : Snapshot width)
    {a b : Row width} (ha : a ∈ snapshot.rows) (hb : b ∈ snapshot.rows)
    (key : a.rowid = b.rowid) : a = b := by
  obtain ⟨rows, unique⟩ := snapshot
  induction rows with
  | nil => simp at ha
  | cons row rest ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at unique
    change a ∈ row :: rest at ha
    change b ∈ row :: rest at hb
    rcases List.mem_cons.mp ha with rfl | memA
    · rcases List.mem_cons.mp hb with rfl | memB
      · rfl
      · exact False.elim (unique.1 ⟨b, memB, key.symm⟩)
    · rcases List.mem_cons.mp hb with rfl | memB
      · exact False.elim (unique.1 ⟨a, memA, key⟩)
      · exact ih unique.2 memA memB

theorem finish_eq_reference {width : Nat} {query : Query width} {plan : Plan}
    {snapshot : Snapshot width} {rows : Relation width} {dir : Direction}
    (honest : Honest query plan snapshot rows) (ordered : query.input.orderBy = some dir) :
    query.finish plan rows = query.reference snapshot := by
  have sortedFinish : (query.finish plan rows).Pairwise (fun a b => dir.before a b = true) := by
    by_cases consumed : plan.orderByConsumed = true
    · simpa [Query.finish, ordered, consumed] using (honest.order consumed dir ordered).filter _
    · simpa [Query.finish, ordered, consumed] using direction_sorted dir _
  have sameRows := (finish_perm honest).trans
    (List.mergeSort_perm (query.matchingRows snapshot) dir.before).symm
  simp only [Query.reference, ordered]
  apply sameRows.eq_of_pairwise _ sortedFinish (direction_sorted dir _)
  intro a b ha hb ab ba
  apply Snapshot.eq_of_rowid snapshot
  · exact (List.mem_filter.mp ((finish_perm honest).subset ha)).1
  · exact (List.mem_filter.mp (List.mem_mergeSort.mp hb)).1
  · cases dir <;> simp only [Direction.before, decide_eq_true_eq] at ab ba
    · exact Int64.le_antisymm ab ba
    · exact Int64.le_antisymm ba ab

theorem runChecked_eq_reference {width : Nat} {table : Table width} {query : Query width}
    {dir : Direction} {result : Relation width} (ordered : query.input.orderBy = some dir)
    (success : table.runChecked query = .ok result) :
    result = query.reference table.snapshot := by
  unfold Table.runChecked at success
  cases started : table.startQuery query with
  | error err => simp [started, bind, Except.bind] at success
  | ok state =>
    obtain ⟨plan, cursor⟩ := state
    cases scanned : cursor.scanRows with
    | error err => simp [started, scanned, bind, Except.bind] at success
    | ok rows =>
      by_cases checked : checkHonesty query plan table.snapshot rows = true
      · simp [started, scanned, checked, bind, Except.bind, pure, Except.pure] at success
        exact success.symm.trans (finish_eq_reference (checkHonesty_iff.mp checked) ordered)
      · simp [started, scanned, checked, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at success

end Silmaril.Proofs.Formats.Sqlite.VirtualTable
