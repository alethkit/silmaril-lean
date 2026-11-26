module

public import Mathlib.CategoryTheory.Functor.Basic

/-! Schemas specify column identities and type codes. A column map sends each source
column to a target column with the same label. Rows pull back along these maps. -/

@[expose] public section

namespace Silmaril.Relational

universe u v w x

/-- A map of indexed labels. Labels can include both a name and a type code. -/
structure ColumnMap {I : Type u} {J : Type v} {Label : Type w}
    (source : I → Label) (target : J → Label) where
  index : I → J
  label_eq : ∀ i, target (index i) = source i

namespace ColumnMap

variable {I : Type u} {J : Type v} {K : Type w} {Label : Type x}
variable {source : I → Label} {target : J → Label} {next : K → Label}

def id (labels : I → Label) : ColumnMap labels labels :=
  ⟨fun i => i, fun _ => rfl⟩

def comp (f : ColumnMap source target) (g : ColumnMap target next) : ColumnMap source next :=
  ⟨fun i => g.index (f.index i), fun i => (g.label_eq (f.index i)).trans (f.label_eq i)⟩

@[ext] theorem ext {f g : ColumnMap source target} (h : f.index = g.index) : f = g := by
  cases f; cases g; cases h; rfl

end ColumnMap

/-- A named schema has one column per occupied name, over an arbitrary name type. -/
structure NamedSchema (Name : Type u) (Kind : Type v) where
  present : Name → Prop
  kind : {name // present name} → Kind

namespace NamedSchema

variable {Name : Type u} {Kind : Type v}

abbrev Index (schema : NamedSchema Name Kind) := {name // schema.present name}

def label (schema : NamedSchema Name Kind) (column : schema.Index) : Name × Kind :=
  (column.val, schema.kind column)

instance : CategoryTheory.Category (NamedSchema Name Kind) where
  Hom s t := ColumnMap s.label t.label
  id s := ColumnMap.id s.label
  comp := ColumnMap.comp
  id_comp _ := ColumnMap.ext rfl
  comp_id _ := ColumnMap.ext rfl
  assoc _ _ _ := ColumnMap.ext rfl

end NamedSchema

/-- A positional schema has an explicit width and assigns a kind to each position. -/
structure PositionalSchema (Kind : Type v) where
  width : Nat
  kind : Fin width → Kind

namespace PositionalSchema

variable {Kind : Type v}

instance : CategoryTheory.Category (PositionalSchema Kind) where
  Hom s t := ColumnMap s.kind t.kind
  id s := ColumnMap.id s.kind
  comp := ColumnMap.comp
  id_comp _ := ColumnMap.ext rfl
  comp_id _ := ColumnMap.ext rfl
  assoc _ _ _ := ColumnMap.ext rfl

end PositionalSchema

/-- A finite named schema with an explicit ordering of its occupied names.
The equivalence ensures that every occupied name has exactly one position. -/
structure NamedPositionalSchema (Name : Type u) (Kind : Type v) where
  named : NamedSchema Name Kind
  width : Nat
  column : Fin width ≃ named.Index

namespace NamedPositionalSchema

variable {Name : Type u} {Kind : Type v}

def positional (schema : NamedPositionalSchema Name Kind) : PositionalSchema Kind :=
  ⟨schema.width, schema.named.kind ∘ schema.column⟩

open CategoryTheory

/-- Arrows preserve column names and kinds. The enumerations determine the induced position map. -/
instance : Category (NamedPositionalSchema Name Kind) where
  Hom s t := s.named ⟶ t.named
  id s := 𝟙 s.named
  comp f g := f ≫ g
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

def forgetPositions : NamedPositionalSchema Name Kind ⥤ NamedSchema Name Kind where
  obj := named
  map f := f

def positionMap {s t : NamedPositionalSchema Name Kind} (f : s ⟶ t) :
    s.positional ⟶ t.positional where
  index i := t.column.symm (f.index (s.column i))
  label_eq i := by
    change t.named.kind (t.column (t.column.symm (f.index (s.column i)))) = s.named.kind (s.column i)
    rw [t.column.apply_symm_apply]
    exact congrArg Prod.snd (f.label_eq (s.column i))

def forgetNames : NamedPositionalSchema Name Kind ⥤ PositionalSchema Kind where
  obj := positional
  map := positionMap
  map_id s := ColumnMap.ext (funext fun i => s.column.symm_apply_apply i)
  map_comp {s t z} f g := ColumnMap.ext (funext fun i => by
    change z.column.symm (g.index (f.index (s.column i))) =
      z.column.symm (g.index (t.column (t.column.symm (f.index (s.column i)))))
    rw [t.column.apply_symm_apply])

end NamedPositionalSchema

end Silmaril.Relational
