module
public import Silmaril.Formats.Sqlite.VirtualTable.Lifecycle
import Silmaril.Proofs.Formats.Sqlite.VirtualTable.Query

public section
namespace Silmaril.Formats.Sqlite.VirtualTable

theorem checkHonesty_iff {width : Nat} {query : Query width} {plan : Plan}
    {snapshot : Snapshot width} {rows : Relation width} :
    checkHonesty query plan snapshot rows = true ↔ Honest query plan snapshot rows :=
  Proofs.Formats.Sqlite.VirtualTable.checkHonesty_iff

theorem scanRows_trace {width : Nat} {cursor : Cursor width} {rows : Relation width} :
    cursor.scanRows = .ok rows ↔ ScanTrace cursor rows :=
  ⟨Proofs.Formats.Sqlite.VirtualTable.scanRows_trace, Proofs.Formats.Sqlite.VirtualTable.trace_scanRows⟩

theorem Direction.sorted {width : Nat} (dir : Direction) (rows : Relation width) :
    (dir.sort rows).Pairwise (fun a b => dir.before a b = true) :=
  Proofs.Formats.Sqlite.VirtualTable.direction_sorted dir rows

theorem finish_perm {width : Nat} {query : Query width} {plan : Plan}
    {snapshot : Snapshot width} {rows : Relation width}
    (honest : Honest query plan snapshot rows) :
    (query.finish plan rows).Perm (query.matchingRows snapshot) :=
  Proofs.Formats.Sqlite.VirtualTable.finish_perm honest

theorem finish_eq_reference {width : Nat} {query : Query width} {plan : Plan}
    {snapshot : Snapshot width} {rows : Relation width} {dir : Direction}
    (honest : Honest query plan snapshot rows) (ordered : query.input.orderBy = some dir) :
    query.finish plan rows = query.reference snapshot :=
  Proofs.Formats.Sqlite.VirtualTable.finish_eq_reference honest ordered

theorem runChecked_eq_reference {width : Nat} {table : Table width} {query : Query width}
    {dir : Direction} {result : Relation width} (ordered : query.input.orderBy = some dir)
    (success : table.runChecked query = .ok result) :
    result = query.reference table.snapshot :=
  Proofs.Formats.Sqlite.VirtualTable.runChecked_eq_reference ordered success

end Silmaril.Formats.Sqlite.VirtualTable
