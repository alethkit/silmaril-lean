module

public import Silmaril.Formats.Sqlite.BTree.LeafWrite.Defs
import Silmaril.Formats.Sqlite.BTree.LeafWrite.Thms
import Silmaril.Formats.Sqlite.File.Thms

public section
namespace Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.Materialize

open Silmaril.Formats Silmaril.Formats.Sqlite

private theorem slice_middle (before middle after : List UInt8) :
    let source := Bytes.ofList (before ++ (middle ++ after))
    let view := File.View.ofBytes source
    ∃ part, view.sub? before.length middle.length = some part ∧
      part.materialize = Bytes.ofList middle := by
  let source := Bytes.ofList (before ++ (middle ++ after))
  let view := File.View.ofBytes source
  have bound : before.length + middle.length ≤ source.length := by
    simp [source]
  let part : File.View := ⟨source, before.length, middle.length, bound⟩
  refine ⟨part, ?_, ?_⟩
  · change view.sub? before.length middle.length = some part
    unfold view File.View.sub? File.View.ofBytes
    rw [dite_eq_left bound]
    simp [part]
  · change Bytes.mk ((before ++ (middle ++ after)).toByteArray.extract
      before.length (before.length + middle.length)) = Bytes.mk middle.toByteArray
    apply congrArg Bytes.mk
    simp only [List.toByteArray_append]
    have first : before.length = before.toByteArray.size := List.size_toByteArray.symm
    change (before.toByteArray ++ (middle.toByteArray ++ after.toByteArray)).extract
      (before.length + 0) (before.length + middle.length) = _
    rw [ByteArray.extract_append_size_add' first]
    exact ByteArray.extract_append_eq_left List.size_toByteArray.symm

private theorem offsets_length (start : Nat) (cells : List (List UInt8)) :
    (BTree.LeafWrite.offsets start cells).length = cells.length := by
  induction cells generalizing start with
  | nil => rfl
  | cons cell tail ih => simp [BTree.LeafWrite.offsets, ih]

private theorem pointers_length (pointers : List Nat) :
    (pointers.flatMap (File.Write.be 2)).length = 2 * pointers.length := by
  induction pointers with
  | nil => rfl
  | cons pointer tail ih =>
    simp [List.flatMap_cons, ih]
    omega

private theorem layout_cell_bytes {leading page cell : List UInt8} {cells : List (List UInt8)}
    (slot : Nat) (accepted : BTree.LeafWrite.layout leading cells = .ok page)
    (found : cells[slot]? = some cell) :
    let view := File.View.ofBytes (Bytes.ofList page)
    let offset := File.Write.pageSize - cells.flatten.length + (cells.take slot).flatten.length
    ∃ part, view.sub? offset cell.length = some part ∧ part.materialize = Bytes.ofList cell := by
  obtain ⟨within, cellAt⟩ := List.getElem?_eq_some_iff.mp found
  have dropped : cells.drop slot = cell :: cells.drop (slot + 1) := by
    rw [List.drop_eq_getElem_cons within, cellAt]
  have flat : cells.flatten =
      (cells.take slot).flatten ++ (cell ++ (cells.drop (slot + 1)).flatten) := by
    calc
      cells.flatten = (cells.take slot ++ cells.drop slot).flatten := by
        rw [List.take_append_drop]
      _ = _ := by rw [dropped, List.flatten_append, List.flatten_cons]
  simp only [BTree.LeafWrite.layout] at accepted
  split at accepted
  next capacity =>
    cases accepted
    let content := File.Write.pageSize - cells.flatten.length
    let used := leading.length + 8 + 2 * cells.length
    let header := leading ++ [13, 0, 0] ++ File.Write.be 2 cells.length ++
      File.Write.be 2 content ++ [0] ++ (BTree.LeafWrite.offsets content cells).flatMap (File.Write.be 2) ++
      List.replicate (content - used) 0
    let prior := header ++ (cells.take slot).flatten
    let after := (cells.drop (slot + 1)).flatten
    have room : used ≤ content := by dsimp [used, content]; omega
    have headerLength : header.length = content := by
      simp only [header, List.length_append, List.length_cons, List.length_nil,
        List.length_replicate, File.Write.be_length, pointers_length, offsets_length]
      dsimp [used] at room ⊢
      omega
    have position : prior.length = content + (cells.take slot).flatten.length := by
      simp [prior, headerLength]
    have serial : header ++ cells.flatten = prior ++ (cell ++ after) := by
      calc
        header ++ cells.flatten =
          header ++ ((cells.take slot).flatten ++ (cell ++ (cells.drop (slot + 1)).flatten)) :=
            congrArg (header ++ ·) flat
        _ = _ := by simp [prior, after, List.append_assoc]
    change ∃ part, (File.View.ofBytes (Bytes.ofList (header ++ cells.flatten))).sub?
      (content + (cells.take slot).flatten.length) cell.length = some part ∧
      part.materialize = Bytes.ofList cell
    rw [serial, ← position]
    exact slice_middle prior cell after
  next => cases accepted

theorem layout_pointer_materialize {leading page cell : List UInt8} {cells : List (List UInt8)}
    (slot : Nat) (accepted : BTree.LeafWrite.layout leading cells = .ok page)
    (found : cells[slot]? = some cell) :
    let source := Bytes.ofList page
    let view := File.View.ofBytes source
    let offset := File.Write.pageSize - cells.flatten.length + (cells.take slot).flatten.length
    view.be? (leading.length + 8 + 2 * slot) 2 = some offset ∧
      ∃ part, view.sub? offset cell.length = some part ∧
        part.source = source ∧ part.start = offset ∧ part.length = cell.length ∧
        part.materialize = Bytes.ofList cell := by
  refine ⟨BTree.LeafWrite.layout_pointer slot accepted (List.getElem?_eq_some_iff.mp found).1, ?_⟩
  obtain ⟨part, sliced, bytes⟩ := layout_cell_bytes slot accepted found
  obtain ⟨source, start, length, _⟩ := File.View.sub?_spec _ part _ _ sliced
  exact ⟨part, sliced, source, by simpa [File.View.ofBytes] using start, length, bytes⟩

end Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.Materialize
