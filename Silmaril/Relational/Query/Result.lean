module

public import Mathlib.Data.Multiset.Defs
public import Mathlib.Data.Set.Defs

/-! # Query results and streaming executions -/

@[expose] public section

namespace Silmaril.Relational

/-- The choice of collection fixes the equality of materialized rows. A relation
observes membership, a finite bag also observes multiplicity, and a list also
observes order. An ordering guarantee can be recorded separately in metadata. -/
inductive Rows (Row : Type*) where
  | relation (rows : Set Row)
  | bag (rows : Multiset Row)
  | ordered (rows : List Row)

namespace Rows

/-- Retain membership and discard multiplicity and position. -/
def support {Row : Type*} : Rows Row → Set Row
  | .relation rows => rows
  | .bag rows => {row | row ∈ rows}
  | .ordered rows => {row | row ∈ rows}

/-- Keep the multiplicities of an ordered output while forgetting positions. -/
def bagOfList {Row : Type*} (rows : List Row) : Rows Row := .bag (rows : Multiset Row)

end Rows

/-- Schema and client-chosen metadata. The latter can carry an ordering guarantee,
column labels, or any other information exposed by the engine. -/
structure ResultMetadata (Schema Annotation : Type*) where
  schema : Schema
  annotation : Annotation

/-- Successful materialized results. `Except Error (Output …)` also observes
defined query errors, including any metadata the error type carries. -/
inductive Output (Row Scalar Schema Annotation : Type*) where
  | rows (metadata : ResultMetadata Schema Annotation) (data : Rows Row)
  | scalar (metadata : ResultMetadata Schema Annotation) (value : Scalar)

/-- One streaming step. A skipped step advances the cursor without yielding a
row. Termination and errors expose a caller-chosen final observation. -/
inductive StreamStep (Cursor Row Error Final : Type*) where
  | yield (row : Row) (next : Cursor)
  | skip (next : Cursor)
  | done (final : Final)
  | error (error : Error) (final : Final)

/-- A finite prefix observes the yielded rows to date, including on runs that
have yet to terminate. Cursor-only steps do not appear in the prefix. -/
inductive StreamPrefix {Cursor Row Error Final : Type*}
    (step : Cursor → StreamStep Cursor Row Error Final → Prop) :
    Cursor → List Row → Prop where
  | nil (cursor : Cursor) : StreamPrefix step cursor []
  | skip {cursor next rows} (h : step cursor (.skip next))
      (tail : StreamPrefix step next rows) : StreamPrefix step cursor rows
  | yield {cursor row next rows} (h : step cursor (.yield row next))
      (tail : StreamPrefix step next rows) : StreamPrefix step cursor (row :: rows)

/-- A finite stream observation includes rows yielded before a defined error. -/
structure StreamResult (Row Error Final : Type*) where
  rows : List Row
  status : Except Error Unit
  final : Final

/-- A finite drain of a possibly nondeterministic stream. Infinite executions
do not produce these terminal observations. -/
inductive StreamDrains {Cursor Row Error Final : Type*}
    (step : Cursor → StreamStep Cursor Row Error Final → Prop) :
    Cursor → StreamResult Row Error Final → Prop where
  | done {cursor final} (h : step cursor (.done final)) :
      StreamDrains step cursor ⟨[], .ok (), final⟩
  | error {cursor error final} (h : step cursor (.error error final)) :
      StreamDrains step cursor ⟨[], .error error, final⟩
  | skip {cursor next result} (h : step cursor (.skip next))
      (tail : StreamDrains step next result) : StreamDrains step cursor result
  | yield {cursor row next result} (h : step cursor (.yield row next))
      (tail : StreamDrains step next result) :
      StreamDrains step cursor { result with rows := row :: result.rows }

end Silmaril.Relational
