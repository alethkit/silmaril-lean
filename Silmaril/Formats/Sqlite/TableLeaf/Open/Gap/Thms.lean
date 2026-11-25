module

public import Silmaril.Formats.Sqlite.TableLeaf.Defs
import Silmaril.Proofs.Formats.Sqlite.TableLeaf.Open.Gap.Read

public section
namespace Silmaril.Formats.Sqlite.TableLeaf

/-- Agreement outside the two intervals between pointer arrays and cell content
preserves the complete ordinary opener result for 1024-byte images. The interval
endpoints use the actual leaf fields. The catalogue interval ends at or before
the first physical page boundary even when its content field is malformed. -/
theorem open?_gap_eq (left right : Bytes) (leftSize : left.length = 1024)
    (rightSize : right.length = 1024)
    (catalogueCount catalogueContent tableCount tableContent : Nat)
    (catCount : (File.View.ofBytes left).be? 103 2 = some catalogueCount)
    (catContent : (File.View.ofBytes left).be? 105 2 = some catalogueContent)
    (tabCount : (File.View.ofBytes left).be? 515 2 = some tableCount)
    (tabContent : (File.View.ofBytes left).be? 517 2 = some tableContent)
    (same : ∀ i, i < 1024 →
      ¬ (108 + 2 * catalogueCount ≤ i ∧ i < catalogueContent ∧ i < 512) →
      ¬ (520 + 2 * tableCount ≤ i ∧ i < 512 + tableContent) →
        (File.View.ofBytes left).get? i = (File.View.ofBytes right).get? i) :
    TableLeaf.open? left = TableLeaf.open? right :=
  Silmaril.Proofs.Formats.Sqlite.TableLeaf.Open.Gap.open?_gap_eq left right leftSize rightSize
    catalogueCount catalogueContent tableCount tableContent catCount catContent tabCount tabContent same

end Silmaril.Formats.Sqlite.TableLeaf
