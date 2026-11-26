module

public import Silmaril.Formats.Sqlite.Record.Defs
import Silmaril.Proofs.Formats.Sqlite.Record.Header.Fuel

public section
namespace Silmaril.Formats.Sqlite.Record

/-- After a successful header read, the code count is bounded by both the
original fuel and the remaining bytes. The same code list is recovered with
any fuel at least that count, and less fuel gives rejection. -/
theorem headerAux?_exact_fuel (source : File.View) (stop budget offset : Nat) {codes : List Nat}
    (parsed : headerAux? source stop budget offset = some codes) :
    codes.length ≤ budget ∧ offset + codes.length ≤ stop ∧
    ∀ fuel, headerAux? source stop fuel offset =
      if codes.length ≤ fuel then some codes else none :=
  Silmaril.Proofs.Formats.Sqlite.Record.Header.headerAux?_exact_fuel source stop budget offset parsed

/-- Any two fuels covering the remaining byte count give the same ordinary
header result, including rejection. -/
theorem headerAux?_fuel_irrel (source : File.View) (stop offset left right : Nat)
    (leftEnough : stop - offset ≤ left) (rightEnough : stop - offset ≤ right) :
    headerAux? source stop left offset = headerAux? source stop right offset :=
  Silmaril.Proofs.Formats.Sqlite.Record.Header.headerAux?_fuel_irrel
    source stop offset left right leftEnough rightEnough

end Silmaril.Formats.Sqlite.Record
