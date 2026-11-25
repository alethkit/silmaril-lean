module

public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Functions.Defs
public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Scalars.Defs

/-! # Tuples, character strings and records as mathematical functions -/

@[expose] public section

namespace Silmaril.Logic.Temporal.TLA.Data.Tagged

universe u

/-- Tuples are graphs with integer keys from one through the length. -/
noncomputable def Graph.tuple (xs : List Value.{u}) : Graph.{u} :=
  ofFn (SetData.intRange 1 xs.length) fun k =>
    let i := (k.asInt.getD 1).toNat - 1
    xs[i]?.getD (.set .empty)

def Value.character (c : Char) : Value.{u} :=
  .tagged .character (natCode c.toNat)

noncomputable def Value.tuple (xs : List Value.{u}) : Value.{u} :=
  .function (Graph.tuple xs)

/-- A string is a tuple of character values. -/
noncomputable def Value.string (s : String) : Value.{u} :=
  .tuple (s.toList.map Value.character)

/-- A record takes a finite list of field names and a value expression on those fields. -/
noncomputable def Graph.record (fields : List String) (body : String → Value.{u}) : Graph.{u} :=
  ofFn (SetData.enum (fields.map Value.string)) fun k =>
    ((decode Value.string k).map body).getD (.set .empty)

noncomputable def Value.record (fields : List String) (body : String → Value.{u}) : Value.{u} :=
  .function (Graph.record fields body)

end Silmaril.Logic.Temporal.TLA.Data.Tagged
