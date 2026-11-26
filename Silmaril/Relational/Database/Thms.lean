module

public import Silmaril.Relational.Database.Defs
import Silmaril.Proofs.Relational.Database.Recovery

/-! Public relationships between dependent, packed, constrained and dynamic databases. -/

@[expose] public section

namespace Silmaril.Relational.Database

universe u v w x y

variable {Name : Type u} {Schema : Type v} {Tables : Schema → Type w} {Observation : Type x}

@[simp] theorem unpack_pack (db : Dependent Name Tables) : db.pack.unpack = db :=
  Proofs.Relational.Database.unpack_pack db

@[simp] theorem pack_unpack (db : Packed Name Tables) : (Packed.unpack db).pack = db :=
  Proofs.Relational.Database.pack_unpack db

/-- Splitting a packed database into its catalog and dependent payloads preserves all entries. -/
def dependentEquivPacked : Dependent Name Tables ≃ Packed Name Tables :=
  ⟨Dependent.pack, Packed.unpack, unpack_pack, pack_unpack⟩

@[simp] theorem catalog_pack (db : Dependent Name Tables) : db.pack.catalog = db.fst :=
  congrArg Sigma.fst (unpack_pack db)

@[simp] theorem map_eq_none_iff {A : Type v} {B : Type w} (f : A → B) (db : Partial Name A)
    (name : Name) : Partial.map f db name = none ↔ db name = none :=
  Option.map_eq_none_iff

@[simp] theorem erase_eq_none_iff (encode : (schema : Schema) → Tables schema → Observation)
    (db : Packed Name Tables) (name : Name) :
    Packed.erase encode db name = none ↔ db name = none := Option.map_eq_none_iff

/-- Erasure preserves precisely the occupied names. -/
def supportMap {A : Type v} {B : Type w} (f : A → B) (db : Partial Name A) :
    Support db ≃ Support (Partial.map f db) where
  toFun n := ⟨n.val, fun h => n.property ((map_eq_none_iff f db n.val).mp h)⟩
  invFun n := ⟨n.val, fun h => n.property ((map_eq_none_iff f db n.val).mpr h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem Enumeration.finite {A : Type v} {db : Partial Name A} (enum : Enumeration db) :
    FiniteSupport db := Finite.of_equiv (Fin enum.size) enum.names

@[simp] theorem catalog_eraseConstraints (valid : (schema : Schema) → Tables schema → Prop)
    (db : Packed Name (fun schema => Constrained (Tables schema) (valid schema))) :
    Packed.catalog (eraseConstraints valid db) = Packed.catalog db := by
  funext name
  exact Option.map_map _ _ (db name)

theorem erase_eraseConstraints (valid : (schema : Schema) → Tables schema → Prop)
    (db : Packed Name (fun schema => Constrained (Tables schema) (valid schema)))
    (encode : (schema : Schema) → Tables schema → Observation) :
    Packed.erase encode (eraseConstraints valid db) =
      Packed.erase (fun schema table => encode schema table.val) db := by
  funext name
  exact Option.map_map _ _ (db name)

theorem recoverable_of_injective (encode : (schema : Schema) → Tables schema → Observation)
    (db : Packed Name Tables)
    (injective : Function.Injective (fun entry : Sigma Tables => encode entry.fst entry.snd)) :
    Recoverable encode (Packed.erase encode db) :=
  Proofs.Relational.Database.recoverable_of_injective encode db injective

@[simp] theorem recover_eq_none_iff (encode : (schema : Schema) → Tables schema → Observation)
    (db : Dynamic Name Observation) (h : Recoverable encode db) (name : Name) :
    recover encode db h name = none ↔ db name = none := Option.pmap_eq_none_iff

@[simp] theorem erase_recover (encode : (schema : Schema) → Tables schema → Observation)
    (db : Dynamic Name Observation) (h : Recoverable encode db) :
    Packed.erase encode (recover encode db h) = db :=
  Proofs.Relational.Database.erase_recover encode db h

@[simp] theorem recover_erase (encode : (schema : Schema) → Tables schema → Observation)
    (db : Packed Name Tables) (h : Recoverable encode (Packed.erase encode db)) :
    recover encode (Packed.erase encode db) h = db :=
  Proofs.Relational.Database.recover_erase encode db h

end Silmaril.Relational.Database
