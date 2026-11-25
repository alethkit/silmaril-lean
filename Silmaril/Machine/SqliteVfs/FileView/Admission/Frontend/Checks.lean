module

import Silmaril.Machine.SqliteVfs.FileView.Admission.Frontend.Thms
meta import Silmaril.Machine.SqliteVfs.FileView.Admission.Frontend.Defs
meta import Silmaril.Formats.Sqlite.Shell.Defs
meta import Silmaril.Formats.Sqlite.TableLeaf.Defs
meta import Silmaril.Machine.SqliteVfs.FileView.Admission.VdbeLeaf.Defs
meta import Silmaril.Machine.SqliteVfs.FileView.VdbeLeaf.Defs

namespace Silmaril.Machine.SqliteVfs.FileView.Admission.Frontend

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SqliteVfs
open _root_.Silmaril.Machine.SqliteVfs.FileView.Admission.VdbeLeaf (btreeHeaderOffset)

private def leaf (base : Nat) (aliasType : UInt8) : File.View :=
  File.View.ofBytes ⟨⟨Array.replicate base 0 ++
    #[13, 0, 0, 0, 1, 1, 250, 0, 1, 250] ++
    Array.replicate (496 - base) 0 ++ #[4, 7, 3, aliasType, 1, 5]⟩⟩

private def matching (base : Nat) : Bool :=
  match query (leaf base 0) base "select amount,id from sample where id=7 order by id desc" with
  | .ok result => decide (result.columns = ["amount", "id"] ∧ result.rows = [[5, 7]])
  | _ => false

#guard matching (btreeHeaderOffset 1)
#guard matching (btreeHeaderOffset 2)

#guard match query (leaf 0 8) 0 "select id from sample" with
  | .error .unreadableLeaf => true
  | _ => false

#guard match query (leaf 0 8) 0 "drop table sample" with
  | .error .unsupportedSql => true
  | _ => false

-- The leaf adapter supplies two integer columns. Exercise error transport
-- directly at the execution boundary with a supplied non-integer row.
private def malformedTable : Vdbe.Table :=
  BTree.Query.ReadModel.ofList [(7, [.integer 7, .text "bad"])]

example : (match executeQuery malformedTable { columns := [.amount] } with
  | .error (.execution message) => message == "unexpected VM row"
  | _ => false) = true := by decide

#print axioms query_eq_of_leaf_decode
#print axioms parsed_image_page_fill_query

end Silmaril.Machine.SqliteVfs.FileView.Admission.Frontend
