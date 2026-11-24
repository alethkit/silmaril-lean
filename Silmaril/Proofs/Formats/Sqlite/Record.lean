module

public import Silmaril.Formats.Sqlite.Record.Defs

public section

namespace Silmaril.Proofs.Formats.Sqlite.Record

open Silmaril.Formats Silmaril.Formats.Sqlite Silmaril.Formats.Sqlite.Record

theorem serialType_text (length : Nat) : serialType (13 + 2*length) = .text length := by
  unfold serialType
  split <;> simp_all <;> omega

end Silmaril.Proofs.Formats.Sqlite.Record
