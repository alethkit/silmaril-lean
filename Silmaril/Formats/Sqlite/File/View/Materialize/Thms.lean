module

public import Silmaril.Formats.Sqlite.File.Defs
import Silmaril.Proofs.Formats.Sqlite.File.View.Materialize.Read

public section
namespace Silmaril.Formats.Sqlite.File.View

/-- Materializing a bounded view preserves its byte length. -/
theorem materialize_length (view : View) : view.materialize.length = view.length :=
  Silmaril.Proofs.Formats.Sqlite.File.View.materialize_length view

/-- At an admitted offset, the copied byte equals the view's byte. -/
theorem materialize_get? (view : View) (i : Nat) (inside : i < view.length) :
    view.materialize.toList[i]? = view.get? i :=
  Silmaril.Proofs.Formats.Sqlite.File.View.materialize_get? view i inside

/-- Matching length and bytes recover the exact materialization of a view. -/
theorem ofList_eq_materialize (view : View) (bytes : List UInt8) (length : bytes.length = view.length)
    (equal : ∀ i, i < view.length → bytes[i]? = view.get? i) :
    Silmaril.Formats.Bytes.ofList bytes = view.materialize :=
  Silmaril.Proofs.Formats.Sqlite.File.View.ofList_eq_materialize view bytes length equal

end Silmaril.Formats.Sqlite.File.View
