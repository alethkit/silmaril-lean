module

public import Silmaril.Semantics.Relational.Table.Organization.Defs

public section

namespace Silmaril.Proofs.Relational.Table
open Silmaril.Relational

universe u v w

variable {I : Type u} {Kind : Type v} {kind : I → Kind} {Cell : Kind → Type w}

theorem toRows_ofRows (rows : Table kind Cell) :
    (AlignedColumns.ofRows rows).toRows = rows := by
  calc
    _ = List.ofFn (fun r : Fin rows.length => rows[r.val]) := by
      apply congrArg (List.ofFn (n := rows.length))
      funext r i
      simp [AlignedColumns.ofRows, List.get_eq_getElem, Fin.cast]
    _ = rows := List.ofFn_getElem

theorem ofRows_toRows (columns : AlignedColumns kind Cell) :
    AlignedColumns.ofRows columns.toRows = columns := by
  apply AlignedColumns.ext (by simp [AlignedColumns.ofRows, AlignedColumns.toRows])
  funext i
  apply List.ext_getElem (by simp [AlignedColumns.ofRows, AlignedColumns.toRows, columns.length_eq])
  intro r _ _
  simp [AlignedColumns.ofRows, AlignedColumns.toRows, List.get_eq_getElem]

end Silmaril.Proofs.Relational.Table
