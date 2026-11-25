module

public import Silmaril.Formats.Sqlite.TableLeaf.Defs
import Silmaril.Proofs.Formats.Sqlite.TableLeaf.Materialize.Read

public section
namespace Silmaril.Formats.Sqlite.TableLeaf

/-- A whole-view copy preserves the packed leaf parser, including rejection,
at the unchanged page-relative base. -/
theorem read_materialized (view : File.View) (base : Nat) :
    read? (File.View.ofBytes view.materialize) base = read? view base :=
  Silmaril.Proofs.Formats.Sqlite.TableLeaf.Materialize.read_materialized view base

end Silmaril.Formats.Sqlite.TableLeaf
