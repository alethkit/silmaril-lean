module

public import Silmaril.Formats.Sqlite.Record.Defs
import Silmaril.Proofs.Formats.Sqlite.Record.Admission.Guards

public section
namespace Silmaril.Formats.Sqlite.Record

/-- At an admitted offset, the column reader succeeds exactly when every
serial type is allowed and their widths fit in the remaining view. -/
theorem columnsAux?_admission (source : File.View) (codes : List Nat) (offset : Nat)
    (inside : offset ≤ source.length) :
    (∃ columns next, columnsAux? source codes offset = some (columns, next)) ↔
    (∀ code ∈ codes, ∀ tag, serialType code ≠ .reserved tag) ∧
      offset + (codes.map fun code => (serialType code).width).sum ≤ source.length :=
  Silmaril.Proofs.Formats.Sqlite.Record.Admission.columnsAux?_admission source codes offset inside

/-- Record admission requires the actual header-size and serial-code reads,
bounded header offsets, allowed serial types and exact payload consumption. -/
theorem parse?_admission (source : File.View) :
    (∃ record, parse? source = some record) ↔
    ∃ size first codes,
      Varint.readNat? source 0 = some (size, first) ∧
      first ≤ size ∧ size ≤ source.length ∧
      headerAux? source size size first = some codes ∧
      (∀ code ∈ codes, ∀ tag, serialType code ≠ .reserved tag) ∧
      size + (codes.map fun code => (serialType code).width).sum = source.length :=
  Silmaril.Proofs.Formats.Sqlite.Record.Admission.parse?_admission source

end Silmaril.Formats.Sqlite.Record
