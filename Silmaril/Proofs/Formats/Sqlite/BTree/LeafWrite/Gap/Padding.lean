module

public import Silmaril.Formats.Sqlite.BTree.LeafWrite.Defs

public section

open Silmaril.Formats Silmaril.Formats.Sqlite

namespace Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.Gap

open BTree.LeafWrite

private theorem pointerBytes_length (start : Nat) (cells : List (List UInt8)) :
    ((offsets start cells).flatMap (File.Write.be 2)).length = 2 * cells.length := by
  induction cells generalizing start with
  | nil => rfl
  | cons cell cells ih =>
    simp only [offsets, List.flatMap_cons, List.length_append, File.Write.be_length, ih,
      List.length_cons]
    omega

theorem layout_gap_slice {leading page : List UInt8} {cells : List (List UInt8)}
    (accepted : layout leading cells = .ok page) :
    let pointerEnd := leading.length + 8 + 2 * cells.length
    let contentStart := File.Write.pageSize - cells.flatten.length
    (Bytes.ofList page).slice? pointerEnd (some contentStart) =
      some (Bytes.replicate (contentStart - pointerEnd) 0) := by
  simp only [layout] at accepted
  split at accepted
  next fits =>
    cases accepted
    dsimp
    let stop := File.Write.pageSize - cells.flatten.length
    let start := leading.length + 8 + 2 * cells.length
    let before := leading ++ [13, 0, 0] ++ File.Write.be 2 cells.length ++
      File.Write.be 2 stop ++ [0] ++ (offsets stop cells).flatMap (File.Write.be 2)
    let padding := List.replicate (stop - start) (0 : UInt8)
    change (Bytes.ofList (before ++ padding ++ cells.flatten)).slice? start (some stop) =
      some (Bytes.replicate (stop - start) 0)
    have beforeLength : before.length = start := by
      simp only [before, start, List.length_append, File.Write.be_length, pointerBytes_length]
      rfl
    have startsBeforeStop : start ≤ stop := by
      dsimp [start, stop]
      omega
    have stopInPage : stop ≤ (Bytes.ofList (before ++ padding ++ cells.flatten)).length := by
      simp only [Bytes.length_ofList, List.length_append, beforeLength, padding, List.length_replicate]
      omega
    rw [Bytes.slice?_of_le (by simpa using startsBeforeStop) (by simpa using stopInPage)]
    simp only [Option.getD_some, Bytes.toList_ofList, List.append_assoc]
    rw [← beforeLength, List.drop_left]
    change some (Bytes.ofList ((padding ++ cells.flatten).take (stop - before.length))) =
      some (Bytes.replicate (stop - before.length) 0)
    rw [beforeLength, ← show padding.length = stop - start from List.length_replicate,
      List.take_left]
    have replicated : (Bytes.replicate padding.length 0).toList = padding := by
      simp [padding]
    exact congrArg some (calc
      Bytes.ofList padding = Bytes.ofList (Bytes.replicate padding.length 0).toList :=
        congrArg Bytes.ofList replicated.symm
      _ = Bytes.replicate padding.length 0 := Bytes.ofList_toList _)
  next => cases accepted

end Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.Gap
