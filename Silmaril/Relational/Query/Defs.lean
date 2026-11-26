module

public import Silmaril.Relational.Query.Result
public import Mathlib.Logic.Embedding.Basic

/-!
# Query denotations

A denotation describes possible observations for each database and query.
Soundness is inclusion, completeness is reverse inclusion, and totality is
existence of an observation at every input. These are separate obligations.
Use an explicit observation function to compare different representations or to
hide details such as ordering, multiplicity, metadata, or final database state.
-/

@[expose] public section

namespace Silmaril.Relational

universe u v

/-- A read-only query denotation indexed by initial database and query. -/
abbrev QueryRel (DB Query Result : Type*) := DB → Query → Result → Prop

/-- A stateful denotation with the initial database first and the final database last. -/
abbrev StatefulQueryRel (DB Query Result : Type*) := DB → Query → Result → DB → Prop

namespace QueryRel

variable {DB Query View Small Large : Type*} {Result : Type u}

/-- Implementation first, specification second. Fewer results refine more results. -/
abbrev Refines (impl spec : QueryRel DB Query Result) : Prop :=
  ∀ {db query result}, impl db query result → spec db query result

abbrev Sound (impl spec : QueryRel DB Query Result) : Prop := impl.Refines spec

abbrev Complete (impl spec : QueryRel DB Query Result) : Prop := spec.Refines impl

/-- Agreement at every initial database and query in the specified fragment. -/
abbrev AgreesOn (fragment : DB → Query → Prop) (left right : QueryRel DB Query Result) : Prop :=
  ∀ {db query}, fragment db query → ∀ result, left db query result ↔ right db query result

/-- Equality of the sets of results, using Lean equality on the result type. -/
abbrev Equivalent (left right : QueryRel DB Query Result) : Prop :=
  left.AgreesOn (fun _ _ => True) right

abbrev Deterministic (sem : QueryRel DB Query Result) : Prop :=
  ∀ {db query left right}, sem db query left → sem db query right → left = right

abbrev Total (sem : QueryRel DB Query Result) : Prop :=
  ∀ db query, ∃ result, sem db query result

/-- Direct image along the chosen observation function. -/
def observe (view : Result → View) (sem : QueryRel DB Query Result) : QueryRel DB Query View :=
  fun db query observed => ∃ result, sem db query result ∧ view result = observed

/-- The graph of a total evaluator. -/
def ofTotal (eval : DB → Query → Result) : QueryRel DB Query Result :=
  fun db query result => eval db query = result

/-- The graph of a partial evaluator. `none` gives the empty set of observations. -/
def ofPartial (eval : DB → Query → Option Result) : QueryRel DB Query Result :=
  fun db query result => eval db query = some result

/-- The terminal observations of all streams started by an input. -/
def ofStream {Cursor Row Error Final : Type*} (start : QueryRel DB Query Cursor)
    (step : Cursor → StreamStep Cursor Row Error Final → Prop) :
    QueryRel DB Query (StreamResult Row Error Final) :=
  fun db query result => ∃ cursor, start db query cursor ∧ StreamDrains step cursor result

/-- The row prefixes of all streams started by an input, with no assertion of termination. -/
def streamPrefixes {Cursor Row Error Final : Type*} (start : QueryRel DB Query Cursor)
    (step : Cursor → StreamStep Cursor Row Error Final → Prop) : QueryRel DB Query (List Row) :=
  fun db query rows => ∃ cursor, start db query cursor ∧ StreamPrefix step cursor rows

/-- Package possible results as a set. This presentation exposes exact membership. -/
def toNondet (sem : QueryRel DB Query Result) : DB → Query → Set Result :=
  fun db query => {result | sem db query result}

def ofNondet (eval : DB → Query → Set Result) : QueryRel DB Query Result :=
  fun db query result => result ∈ eval db query

/-- A relational reading of an effectful evaluator through a specified runner.
Include any observable effects in the result type. -/
def ofMonad {M : Type u → Type v} (run : M Result → Set View)
    (eval : DB → Query → M Result) : QueryRel DB Query View :=
  fun db query observed => observed ∈ run (eval db query)

/-- Relational composition with a continuation on results. -/
def bindResults (sem : QueryRel DB Query Result) (next : Result → Set View) :
    QueryRel DB Query View :=
  fun db query observed => ∃ result, sem db query result ∧ observed ∈ next result

/-- Select the unique result where one exists. This graph is exact for
deterministic relations. The choice is classical. -/
noncomputable def toPartial (sem : QueryRel DB Query Result) : DB → Query → Option Result := by
  classical
  exact fun db query =>
    if h : ∃ result, sem db query result then some (Classical.choose h) else none

/-- Select one allowed result at each input. This graph is exact when the
relation is also deterministic. -/
noncomputable def toTotal (sem : QueryRel DB Query Result) (total : sem.Total) :
    DB → Query → Result :=
  fun db query => Classical.choose (total db query)

/-- Interpret a smaller query language by translating it to a larger one. -/
def restrict (translate : Small → Large) (sem : QueryRel DB Large Result) :
    QueryRel DB Small Result :=
  fun db query => sem db (translate query)

/-- Direct image along a query translation. Queries outside the image have
no specified result. Injectivity is needed for exact read-back. -/
def extend (translate : Small → Large) (sem : QueryRel DB Small Result) :
    QueryRel DB Large Result :=
  fun db query result => ∃ small, translate small = query ∧ sem db small result

end QueryRel

namespace StatefulQueryRel

variable {DB Query Result : Type*}

/-- Observe the result and final database as one outcome. QueryRel comparisons
on this presentation compare both unless an explicit observation hides one. -/
def toQueryRel (sem : StatefulQueryRel DB Query Result) : QueryRel DB Query (Result × DB) :=
  fun db query outcome => sem db query outcome.1 outcome.2

def ofQueryRel (sem : QueryRel DB Query (Result × DB)) : StatefulQueryRel DB Query Result :=
  fun db query result finalDB => sem db query (result, finalDB)

/-- Observe results while hiding the final database. -/
def forgetState (sem : StatefulQueryRel DB Query Result) : QueryRel DB Query Result :=
  sem.toQueryRel.observe Prod.fst

/-- View a read-only semantics as one that returns the initial database. -/
def ofReadOnly (sem : QueryRel DB Query Result) : StatefulQueryRel DB Query Result :=
  fun db query result finalDB => sem db query result ∧ finalDB = db

/-- Read a state evaluator as a relation on the result and final database. -/
def ofStateM {State Value : Type u} (eval : Query → StateM State Value) :
    StatefulQueryRel State Query Value :=
  ofQueryRel (QueryRel.ofTotal fun db query => (eval query).run db)

end StatefulQueryRel

/-- Extend a query-indexed family along an embedding, using a chosen semantics
outside the image. This leaves the database available to the fallback. -/
noncomputable def extendQueries {DB Small Large Value : Type*} (embedding : Small ↪ Large)
    (fallback : DB → Large → Value) (sem : DB → Small → Value) : DB → Large → Value := by
  classical
  exact fun db query =>
    if h : ∃ small, embedding small = query then sem db (Classical.choose h)
    else fallback db query

end Silmaril.Relational
