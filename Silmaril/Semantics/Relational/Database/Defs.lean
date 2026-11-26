module

public import Silmaril.Semantics.Relational.Table.Thms
public import Mathlib.Data.Fintype.EquivFin

/-! A catalog assigns schemas to present names. A packed entry stores its schema
alongside its table, while an erased entry stores only a client-specified observation. -/

@[expose] public section

namespace Silmaril.Relational.Database

universe u v w x y

abbrev Partial (Name : Type u) (Data : Type v) := Name → Option Data

abbrev Catalog (Name : Type u) (Schema : Type v) := Partial Name Schema

/-- The table type at a catalog lookup. Missing names have a single trivial payload. -/
def Payload {Schema : Type v} (Tables : Schema → Type w) : Option Schema → Type w
  | none => PUnit
  | some schema => Tables schema

abbrev Over {Name : Type u} {Schema : Type v} (catalog : Catalog Name Schema)
    (Tables : Schema → Type w) :=
  (name : Name) → Payload Tables (catalog name)

abbrev Dependent (Name : Type u) {Schema : Type v} (Tables : Schema → Type w) :=
  Σ catalog : Catalog Name Schema, Over catalog Tables

/-- Each occupied name carries its own schema and a table of that schema. -/
abbrev Packed (Name : Type u) {Schema : Type v} (Tables : Schema → Type w) :=
  Partial Name (Sigma Tables)

/-- A dynamic database with only the chosen schema-erased observations at occupied names. -/
abbrev Dynamic (Name : Type u) (Observation : Type v) := Partial Name Observation

variable {Name : Type u} {Schema : Type v} {Tables : Schema → Type w}

/-- Look up a typed table given the catalog entry for its name. -/
def Over.lookup {catalog : Catalog Name Schema} (db : Over catalog Tables)
    (name : Name) {schema : Schema} (found : catalog name = some schema) : Tables schema :=
  cast (congrArg (Payload Tables) found) (db name)

def packEntry : (schema : Option Schema) → Payload Tables schema → Option (Sigma Tables)
  | none, _ => none
  | some schema, table => some ⟨schema, table⟩

def unpackPayload (entry : Option (Sigma Tables)) : Payload Tables (entry.map Sigma.fst) :=
  match entry with
  | none => PUnit.unit
  | some entry => entry.snd

def Dependent.pack (db : Dependent Name Tables) : Packed Name Tables :=
  fun name => packEntry (db.fst name) (db.snd name)

def Packed.catalog (db : Packed Name Tables) : Catalog Name Schema :=
  fun name => (db name).map Sigma.fst

def Packed.unpack (db : Packed Name Tables) : Dependent Name Tables :=
  ⟨db.catalog, fun name => unpackPayload (db name)⟩

def Partial.map {A : Type v} {B : Type w} (f : A → B) (db : Partial Name A) :
    Partial Name B :=
  fun name => (db name).map f

/-- Forget entry metadata using the observation chosen by the caller. -/
def Packed.erase {Observation : Type x} (encode : (schema : Schema) → Tables schema → Observation)
    (db : Packed Name Tables) : Dynamic Name Observation :=
  Partial.map (fun entry => encode entry.fst entry.snd) db

def eraseConstraints (valid : (schema : Schema) → Tables schema → Prop)
    (db : Packed Name (fun schema => Constrained (Tables schema) (valid schema))) :
    Packed Name Tables :=
  Partial.map (fun entry => ⟨entry.fst, entry.snd.val⟩) db

/-- The erased database has a unique compatible packed entry at each occupied name. -/
def Recoverable {Observation : Type x} (encode : (schema : Schema) → Tables schema → Observation)
    (db : Dynamic Name Observation) : Prop :=
  ∀ name observation, db name = some observation →
    ∃! entry : Sigma Tables, encode entry.fst entry.snd = observation

/-- Recover by unique existence. Missing names are preserved. -/
noncomputable def recover {Observation : Type x}
    (encode : (schema : Schema) → Tables schema → Observation) (db : Dynamic Name Observation)
    (h : Recoverable encode db) : Packed Name Tables :=
  fun name => (db name).pmap (fun _ unique => Classical.choose unique) (h name)

abbrev Support {A : Type v} (db : Partial Name A) := {name // db name ≠ none}

/-- A proposition asserting that the occupied names form a finite type. -/
abbrev FiniteSupport {A : Type v} (db : Partial Name A) := Finite (Support db)

/-- A concrete ordering of the occupied names, with complete and unique coverage. -/
structure Enumeration {A : Type v} (db : Partial Name A) where
  size : Nat
  names : Fin size ≃ Support db

noncomputable def Enumeration.ofFinite {A : Type v} {db : Partial Name A}
    (finite : FiniteSupport db) : Enumeration db :=
  letI := finite
  letI := Fintype.ofFinite (Support db)
  ⟨Fintype.card (Support db), (Fintype.equivFin (Support db)).symm⟩

end Silmaril.Relational.Database
