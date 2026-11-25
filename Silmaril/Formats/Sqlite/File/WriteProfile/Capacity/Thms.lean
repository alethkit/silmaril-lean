module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Defs
import Silmaril.Proofs.Formats.Sqlite.File.WriteProfile.Capacity.Layout

public section
namespace Silmaril.Formats.Sqlite.WriteProfile.Image

/-- The raw writer accepts a snapshot exactly when the table leaf header,
pointer slots and serialized cells fit in the writer's table page. -/
theorem encode_accepts_iff (snapshot : Snapshot) :
    let cells := snapshot.orderedRows.map fun row =>
      (⟨row.id, Record.Write.amount row.amount⟩ : BTree.LeafWrite.Cell).bytes
    (∃ bytes, encode snapshot = .ok bytes) ↔
      8 + 2 * snapshot.orderedRows.length + cells.flatten.length ≤ File.Write.pageSize :=
  Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.Capacity.encode_accepts_iff snapshot

/-- The raw writer reports `.tablePage .pageFull` exactly when the encoded
table leaf would exceed its page capacity. -/
theorem encode_pageFull_iff (snapshot : Snapshot) :
    let cells := snapshot.orderedRows.map fun row =>
      (⟨row.id, Record.Write.amount row.amount⟩ : BTree.LeafWrite.Cell).bytes
    encode snapshot = .error (.tablePage .pageFull) ↔
      File.Write.pageSize < 8 + 2 * snapshot.orderedRows.length + cells.flatten.length :=
  Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.Capacity.encode_pageFull_iff snapshot

end Silmaril.Formats.Sqlite.WriteProfile.Image
