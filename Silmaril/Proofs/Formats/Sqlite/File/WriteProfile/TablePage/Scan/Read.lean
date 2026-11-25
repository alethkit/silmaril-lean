module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Defs
public import Silmaril.Formats.Sqlite.TableLeaf.Defs
import Silmaril.Formats.Sqlite.BTree.LeafWrite.Thms
import Silmaril.Formats.Sqlite.File.WriteProfile.TablePage.Amount.Thms
import Silmaril.Formats.Sqlite.File.WriteProfile.Thms
import Silmaril.Formats.Sqlite.Record.Write.Thms

public section

open Silmaril.Formats Silmaril.Formats.Sqlite
open Silmaril.Formats.Sqlite.WriteProfile Silmaril.Formats.Sqlite.WriteProfile.Image

namespace Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.TablePage.Scan

private def serialized (row : Row) : List UInt8 :=
  BTree.LeafWrite.Cell.bytes ⟨row.id, Record.Write.amount row.amount⟩

private theorem serialized_length (row : Row) :
    (serialized row).length = 1 + (Varint.encode row.id.toUInt64).toList.length + 11 := by
  have lengthByte : (Varint.encode (UInt64.ofNat 11)).toList = [11] := rfl
  simp only [serialized, BTree.LeafWrite.Cell.bytes, Record.Write.amount_length, lengthByte,
    List.length_append, List.length_cons, List.length_nil, List.length_replicate]
  omega

private def atOffset (start : Nat) (row : Row) : TableLeaf.Cell :=
  ⟨row.id, Bytes.ofList (Record.Write.amount row.amount), start, start + (serialized row).length⟩

private def placed (start : Nat) : List Row → List TableLeaf.Cell
  | [] => []
  | row :: rest => atOffset start row :: placed (start + (serialized row).length) rest

@[simp] private theorem placed_length (start : Nat) (rows : List Row) :
    (placed start rows).length = rows.length := by
  induction rows generalizing start <;> simp [placed, *]

private theorem placed_get (start : Nat) (rows : List Row) (slot : Nat) (valid : slot < rows.length) :
    (placed start rows)[slot]'(by simpa using valid) =
      atOffset (start + ((rows.map serialized).take slot).flatten.length) rows[slot] := by
  induction rows generalizing start slot with
  | nil => simp at valid
  | cons row rest ih =>
    cases slot with
    | zero => simp [placed]
    | succ slot =>
      simp only [placed, List.getElem_cons_succ, List.map_cons, List.take_succ_cons,
        List.flatten_cons, List.length_append, ← Nat.add_assoc]
      exact ih (start + (serialized row).length) slot (by simpa using valid)

private theorem placed_packed (start : Nat) (rows : List Row) :
    TableLeaf.packed start (start + (rows.map serialized).flatten.length) (placed start rows) = true := by
  induction rows generalizing start with
  | nil => simp [placed, TableLeaf.packed]
  | cons row rest ih =>
    simp only [placed, List.map_cons, TableLeaf.packed, atOffset, beq_self_eq_true, Bool.true_and,
      List.flatten_cons, List.length_append, ← Nat.add_assoc]
    exact ih (start + (serialized row).length)

private theorem placed_starts (start : Nat) (rows : List Row) :
    (placed start rows).Pairwise (fun a b => decide (a.start ≤ b.start)) := by
  induction rows generalizing start with
  | nil => simp [placed]
  | cons row rest ih =>
    simp only [placed, List.pairwise_cons, decide_eq_true_eq]
    refine ⟨?_, by simpa only [decide_eq_true_eq] using ih _⟩
    intro cell member
    obtain ⟨slot, valid, rfl⟩ := List.mem_iff_getElem.mp member
    have validRow : slot < rest.length := by simpa using valid
    rw [placed_get _ _ _ validRow]
    simp only [atOffset]
    omega

private theorem ordered_keys (snapshot : Snapshot) :
    snapshot.orderedRows.Pairwise (fun a b => a.id.toInt < b.id.toInt) := by
  have sorted := List.pairwise_mergeSort (le := fun a b : Row => decide (a.id.toInt ≤ b.id.toInt))
    (by intro a b c; simp only [decide_eq_true_eq]; omega)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) snapshot.rows
  have permutation := List.mergeSort_perm snapshot.rows (fun a b => decide (a.id.toInt ≤ b.id.toInt))
  have distinct : (snapshot.orderedRows.map Row.id).Nodup := (permutation.map Row.id).nodup_iff.mpr snapshot.unique
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj less
  have le := List.pairwise_iff_getElem.mp sorted i j hi hj less
  have ne := List.pairwise_iff_getElem.mp distinct i j (by simpa using hi) (by simpa using hj) less
  simp only [decide_eq_true_eq] at le
  change snapshot.orderedRows[i].id.toInt ≤ snapshot.orderedRows[j].id.toInt at le
  simp only [List.getElem_map] at ne
  have different : snapshot.orderedRows[i].id.toInt ≠ snapshot.orderedRows[j].id.toInt :=
    fun eq => ne (Int64.toInt_inj.mp eq)
  omega

private theorem placed_keys (start : Nat) (snapshot : Snapshot) :
    (placed start snapshot.orderedRows).Pairwise (fun a b => a.key.toInt < b.key.toInt) := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj less
  have si : i < snapshot.orderedRows.length := by simpa using hi
  have sj : j < snapshot.orderedRows.length := by simpa using hj
  rw [placed_get _ _ _ si, placed_get _ _ _ sj]
  exact List.pairwise_iff_getElem.mp (ordered_keys snapshot) _ _ si sj less

private theorem mapM_range_of_reads {α : Type} (outputs : List α) (read : Nat → Option α)
    (exactAt : ∀ slot (valid : slot < outputs.length), read slot = some outputs[slot]) :
    (List.range outputs.length).mapM read = some outputs := by
  induction outputs generalizing read with
  | nil => rfl
  | cons output outputs ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.mapM_cons, List.mapM_map]
    rw [exactAt 0 (by simp), ih (read ∘ Nat.succ) (fun slot valid => exactAt (slot + 1) (by simpa))]
    rfl

private theorem admittedGuard {p : Prop} [Decidable p] (h : p) : (guard p : Option Unit) = some () := by
  simp [guard, h]

/-- The actual packed-leaf reader accepts a successfully encoded table page
and reads exactly the ordered cells emitted by the writer. -/
private theorem tablePage_read {snapshot : Snapshot} {page : List UInt8}
    (accepted : tablePage snapshot = .ok page) :
    let used := (snapshot.orderedRows.map serialized).flatten.length
    TableLeaf.read? (File.View.ofBytes (Bytes.ofList page)) 0 =
      some (placed (File.Write.pageSize - used) snapshot.orderedRows) := by
  dsimp only
  let rows := snapshot.orderedRows
  let cells := rows.map serialized
  let content := File.Write.pageSize - cells.flatten.length
  let view := File.View.ofBytes (Bytes.ofList page)
  let decoded := placed content rows
  change TableLeaf.read? view 0 = some decoded
  have layout : BTree.LeafWrite.layout [] cells = .ok page := by
    unfold tablePage BTree.LeafWrite.encode at accepted
    split at accepted
    · simp only [List.map_map, Function.comp_def] at accepted
      exact accepted
    · cases accepted
  have pageLength : view.length = 512 := by simpa [view, File.View.ofBytes] using leaf_length accepted
  have fixed := BTree.LeafWrite.layout_fixed_header layout
  have counts := BTree.LeafWrite.layout_header_fields layout
  dsimp only [List.length_nil, Nat.zero_add] at fixed counts
  change view.get? 0 = some 13 ∧ view.be? 1 2 = some 0 ∧ view.get? 7 = some 0 ∧
    8 + 2 * cells.length ≤ content at fixed
  change view.be? 3 2 = some cells.length ∧ view.be? 5 2 = some content at counts
  have capacity : cells.flatten.length ≤ File.Write.pageSize := by
    have fit := fixed.2.2.2
    dsimp only [content] at fit
    omega
  have contentBound : content ≤ 512 := by exact Nat.sub_le ..
  have ranges : cells.length = decoded.length := by simp [cells, decoded]
  have exactAt (slot : Nat) (valid : slot < decoded.length) :
      (do
        let offset ← view.be? (8 + 2 * slot) 2
        guard (content ≤ offset && offset < 512)
        TableLeaf.cell? view offset) = some decoded[slot] := by
    have rowValid : slot < rows.length := by simpa [decoded] using valid
    have cellValid : slot < cells.length := by simpa [cells] using rowValid
    let row := rows[slot]
    let offset := content + (cells.take slot).flatten.length
    have selected := tablePage_selected_amount slot row.id row.amount accepted
      (getElem?_pos rows slot rowValid)
    dsimp only at selected
    simp only [List.map_map, Function.comp_def] at selected
    change view.be? (8 + 2 * slot) 2 = some offset ∧
      TableLeaf.cell? view offset = some ⟨row.id, Bytes.ofList (Record.Write.amount row.amount),
        offset, offset + (1 + (Varint.encode row.id.toUInt64).toList.length + 11)⟩ ∧ _ at selected
    have prefixFits : (cells.take slot).flatten.length + cells[slot].length ≤ cells.flatten.length := by
      have combined := congrArg (fun parts : List (List UInt8) => parts.flatten.length)
        (List.take_append_drop (slot + 1) cells)
      rw [List.take_succ_eq_append_getElem cellValid] at combined
      simp only [List.flatten_append, List.length_append, List.flatten_cons, List.flatten_nil,
        List.append_nil] at combined
      omega
    have nonempty : 0 < cells[slot].length := by
      rw [List.getElem_map, serialized_length]
      omega
    have inRange : offset < 512 := by
      change content + (cells.take slot).flatten.length < File.Write.pageSize
      dsimp only [content]
      omega
    have lower : content ≤ offset := Nat.le_add_right ..
    rw [placed_get _ _ slot rowValid]
    have admitted : (decide (content ≤ offset) && decide (offset < 512)) = true := by
      simp [lower, inRange]
    simp only [selected.1, Option.bind_eq_bind, Option.bind_some, admittedGuard admitted]
    change TableLeaf.cell? view offset = some (atOffset offset row)
    rw [atOffset, serialized_length]
    exact selected.2.1
  have allCells := mapM_range_of_reads decoded _ exactAt
  rw [← ranges] at allCells
  have order : decoded.mergeSort (fun a b => decide (a.start ≤ b.start)) = decoded :=
    List.mergeSort_of_pairwise (placed_starts content rows)
  have packed : TableLeaf.packed content 512 decoded = true := by
    have full : content + cells.flatten.length = 512 := Nat.sub_add_cancel capacity
    have actual := placed_packed content rows
    change TableLeaf.packed content (content + cells.flatten.length) decoded = true at actual
    rwa [full] at actual
  have keys := placed_keys content snapshot
  change decoded.Pairwise (fun a b => a.key.toInt < b.key.toInt) at keys
  have room : (decide (8 + 2 * cells.length ≤ content) && decide (content ≤ 512)) = true := by
    simp [fixed.2.2.2, contentBound]
  simp only [TableLeaf.read?, Nat.zero_add, pageLength, fixed.1, fixed.2.1, fixed.2.2.1,
    counts.1, counts.2, beq_self_eq_true, Bool.and_self, Option.bind_eq_bind, Option.bind_some,
    admittedGuard True.intro, admittedGuard room]
  change ((List.range cells.length).mapM (fun slot => do
    let offset ← view.be? (8 + 2 * slot) 2
    guard (content ≤ offset && offset < 512)
    TableLeaf.cell? view offset)).bind _ = _
  rw [allCells]
  simp [order, packed, keys, guard]

private theorem placed_rows (start : Nat) (rows : List Row) :
    (placed start rows).mapM TableLeaf.row? = some (rows.map Row.entry) := by
  induction rows generalizing start with
  | nil => rfl
  | cons row rest ih =>
    have read : TableLeaf.row? (atOffset start row) = some row.entry := by
      simp [TableLeaf.row?, atOffset, Record.Write.decode_amount, Row.entry]
    simp [placed, read, ih]

/-- A successfully emitted table page is accepted by the ordinary leaf and row
readers. They return exactly the snapshot entries in signed rowid order. -/
theorem tablePage_read_rows {snapshot : Snapshot} {page : List UInt8}
    (accepted : tablePage snapshot = .ok page) :
    (TableLeaf.read? (File.View.ofBytes (Bytes.ofList page)) 0).bind (List.mapM TableLeaf.row?) =
      some (snapshot.orderedRows.map Row.entry) := by
  rw [tablePage_read accepted]
  exact placed_rows _ _

end Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.TablePage.Scan
