module

public import Silmaril.Formats.Sqlite.BTree.LeafWrite.Defs
import Silmaril.Formats.Sqlite.File.Write.Thms

public section
namespace Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite

open Silmaril.Formats Silmaril.Formats.Sqlite

private theorem get_ofList (source : List UInt8) (index : Nat) :
    (File.View.ofBytes (Bytes.ofList source)).get? index = source[index]? := by
  by_cases fits : index < source.length
  · simp only [File.View.get?, File.View.ofBytes, Bytes.length_ofList, fits, ite_true, Nat.zero_add]
    have listed : (Bytes.ofList source).data.data.toList = source := Bytes.toList_ofList source
    calc
      _ = (Bytes.ofList source).data.data[index]? := rfl
      _ = (Bytes.ofList source).data.data.toList[index]? := Array.getElem?_toList.symm
      _ = _ := by rw [listed]
  · simp [File.View.get?, File.View.ofBytes, fits]

private theorem read_field (before after : List UInt8) (value : Nat)
    (fits : value < 256 ^ 2) :
    (File.View.ofBytes (Bytes.ofList (before ++ (File.Write.be 2 value ++ after)))).be?
      before.length 2 = some value := by
  apply File.Write.be?_be_two _ _ _ fits
  intro i hi
  rw [get_ofList, List.getElem?_append_right (by omega)]
  rw [show before.length + i - before.length = i by omega]
  rw [List.getElem?_append_left (by simpa using hi)]

theorem layout_header_fields {leading page : List UInt8} {cells : List (List UInt8)}
    (accepted : BTree.LeafWrite.layout leading cells = .ok page) :
    let view := File.View.ofBytes (Bytes.ofList page)
    view.be? (leading.length + 3) 2 = some cells.length ∧
      view.be? (leading.length + 5) 2 =
        some (File.Write.pageSize - cells.flatten.length) := by
  simp only [BTree.LeafWrite.layout] at accepted
  split at accepted
  next capacity =>
    cases accepted
    let content := File.Write.pageSize - cells.flatten.length
    let used := leading.length + 8 + 2 * cells.length
    let after := [0] ++ (BTree.LeafWrite.offsets content cells).flatMap (File.Write.be 2) ++
      List.replicate (content - used) 0 ++ cells.flatten
    have countFits : cells.length < 256 ^ 2 := by
      unfold File.Write.pageSize at capacity
      omega
    have contentFits : content < 256 ^ 2 := by
      have bounded := Nat.sub_le File.Write.pageSize cells.flatten.length
      dsimp [content, File.Write.pageSize] at bounded ⊢
      omega
    have priorLength : (leading ++ ([13, 0, 0] : List UInt8)).length = leading.length + 3 := by
      simp
    have priorContentLength :
        (leading ++ [13, 0, 0] ++ File.Write.be 2 cells.length).length = leading.length + 5 := by
      simp
    constructor
    · have field := read_field (leading ++ [13, 0, 0])
          (File.Write.be 2 content ++ after) cells.length countFits
      rw [priorLength] at field
      simpa [after, content, used] using field
    · have field := read_field (leading ++ [13, 0, 0] ++ File.Write.be 2 cells.length)
          after content contentFits
      rw [priorContentLength] at field
      simpa [after, content, used] using field
  next => cases accepted

private theorem read_byte (before after : List UInt8) (byte : UInt8) :
    (File.View.ofBytes (Bytes.ofList (before ++ byte :: after))).get? before.length = some byte := by
  rw [get_ofList, List.getElem?_append_right (Nat.le_refl _)]
  simp

/-- A successful packed writer layout has the table-leaf type, zero freeblock
and fragment fields, and a pointer array that ends at or before cell content. -/
theorem layout_fixed_header {leading page : List UInt8} {cells : List (List UInt8)}
    (accepted : BTree.LeafWrite.layout leading cells = .ok page) :
    let view := File.View.ofBytes (Bytes.ofList page)
    view.get? leading.length = some 13 ∧
      view.be? (leading.length + 1) 2 = some 0 ∧
      view.get? (leading.length + 7) = some 0 ∧
      leading.length + 8 + 2 * cells.length ≤ File.Write.pageSize - cells.flatten.length := by
  simp only [BTree.LeafWrite.layout] at accepted
  split at accepted
  next capacity =>
    cases accepted
    let content := File.Write.pageSize - cells.flatten.length
    let used := leading.length + 8 + 2 * cells.length
    let after := (BTree.LeafWrite.offsets content cells).flatMap (File.Write.be 2) ++
      List.replicate (content - used) 0 ++ cells.flatten
    let fields := File.Write.be 2 cells.length ++ File.Write.be 2 content
    let before := leading ++ [13, 0, 0] ++ fields
    have prefixKind := read_byte leading ([0, 0] ++ fields ++ [0] ++ after) 13
    have priorLength : (leading ++ ([13] : List UInt8)).length = leading.length + 1 := by simp
    have freeblocks := read_field (leading ++ [13]) (fields ++ [0] ++ after) 0 (by decide)
    rw [priorLength] at freeblocks
    have fragments := read_byte before after 0
    have beforeLength : before.length = leading.length + 7 := by simp [before, fields]
    rw [beforeLength] at fragments
    have zeroBytes : File.Write.be 2 0 = [0, 0] := rfl
    refine ⟨?_, ?_, ?_, by omega⟩
    · simpa [fields, after, content, used, List.append_assoc] using prefixKind
    · simpa [zeroBytes, fields, after, content, used, List.append_assoc] using freeblocks
    · simpa [before, fields, after, content, used, List.append_assoc] using fragments
  next => cases accepted


private theorem offsets_prefix (start : Nat) (cells : List (List UInt8)) (slot : Nat)
    (within : slot < cells.length) :
    (BTree.LeafWrite.offsets start cells)[slot]? = some (start + (cells.take slot).flatten.length) := by
  induction cells generalizing start slot with
  | nil => simp at within
  | cons cell tail ih =>
    cases slot with
    | zero => simp [BTree.LeafWrite.offsets]
    | succ index =>
      have bound : index < tail.length := by simpa using within
      simp only [BTree.LeafWrite.offsets, List.getElem?_cons_succ, List.take_succ_cons]
      rw [ih (start + cell.length) index bound]
      simp [Nat.add_assoc]

private theorem read_pointer (before after : List UInt8) (pointers : List Nat)
    (slot value : Nat) (atSlot : pointers[slot]? = some value) (fits : value < 256 ^ 2) :
    (File.View.ofBytes (Bytes.ofList (before ++ (pointers.flatMap (File.Write.be 2) ++ after)))).be?
      (before.length + 2 * slot) 2 = some value := by
  induction pointers generalizing before slot with
  | nil => simp at atSlot
  | cons pointer tail ih =>
    cases slot with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at atSlot
      subst pointer
      simpa [List.flatMap_cons, List.append_assoc] using
        read_field before (tail.flatMap (File.Write.be 2) ++ after) value fits
    | succ index =>
      simp only [List.getElem?_cons_succ] at atSlot
      have field := ih (before ++ File.Write.be 2 pointer) index atSlot
      have indexEq : (before ++ File.Write.be 2 pointer).length + 2 * index =
          before.length + 2 * (index + 1) := by
        simp
        omega
      rw [indexEq] at field
      simpa [List.flatMap_cons, List.append_assoc] using field

theorem layout_pointer {leading page : List UInt8} {cells : List (List UInt8)} (slot : Nat)
    (accepted : BTree.LeafWrite.layout leading cells = .ok page) (within : slot < cells.length) :
    let view := File.View.ofBytes (Bytes.ofList page)
    view.be? (leading.length + 8 + 2 * slot) 2 =
      some (File.Write.pageSize - cells.flatten.length + (cells.take slot).flatten.length) := by
  simp only [BTree.LeafWrite.layout] at accepted
  split at accepted
  next capacity =>
    cases accepted
    let content := File.Write.pageSize - cells.flatten.length
    let used := leading.length + 8 + 2 * cells.length
    let before := leading ++ [13, 0, 0] ++ File.Write.be 2 cells.length ++ File.Write.be 2 content ++ [0]
    let after := List.replicate (content - used) 0 ++ cells.flatten
    let offset := content + (cells.take slot).flatten.length
    have bound : (cells.take slot).flatten.length ≤ cells.flatten.length := by
      have split : cells.flatten = (cells.take slot).flatten ++ (cells.drop slot).flatten := by
        rw [← List.flatten_append, List.take_append_drop]
      rw [split, List.length_append]
      omega
    have fits : offset < 256 ^ 2 := by
      unfold File.Write.pageSize at capacity
      dsimp [offset, content, File.Write.pageSize]
      omega
    have field := read_pointer before after (BTree.LeafWrite.offsets content cells) slot offset
      (offsets_prefix content cells slot within) fits
    have beforeLength : before.length = leading.length + 8 := by
      simp [before]
    rw [beforeLength] at field
    simpa [before, after, offset, content, used] using field
  next => cases accepted

end Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite
