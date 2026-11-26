module

public import Silmaril.Semantics.Relational.Database.Defs

public section

namespace Silmaril.Proofs.Relational.Database
open Silmaril.Relational.Database

universe u v w x

variable {Name : Type u} {Schema : Type v} {Tables : Schema → Type w} {Observation : Type x}
variable (encode : (schema : Schema) → Tables schema → Observation)

theorem unpack_pack (db : Dependent Name Tables) : db.pack.unpack = db := by
  let assemble (entries : Name → (Σ s : Option Schema, Payload Tables s)) : Dependent Name Tables :=
    ⟨fun name => (entries name).fst, fun name => (entries name).snd⟩
  have entry (schema : Option Schema) (table : Payload Tables schema) :
      (⟨_, unpackPayload (packEntry schema table)⟩ : Σ s, Payload Tables s) = ⟨schema, table⟩ := by
    cases schema with
    | none => cases table; rfl
    | some _ => rfl
  exact congrArg assemble (funext fun name => entry (db.fst name) (db.snd name))

theorem pack_unpack (db : Packed Name Tables) : (Packed.unpack db).pack = db := by
  funext name
  show packEntry ((db name).map Sigma.fst) (unpackPayload (db name)) = db name
  cases db name <;> rfl

theorem recoverable_of_injective (db : Packed Name Tables)
    (injective : Function.Injective (fun entry : Sigma Tables => encode entry.fst entry.snd)) :
    Recoverable encode (Packed.erase encode db) := by
  intro name observation found
  obtain ⟨entry, _, rfl⟩ := Option.map_eq_some_iff.mp found
  exact ⟨entry, rfl, fun _ same => injective same⟩

theorem erase_recover (db : Dynamic Name Observation) (h : Recoverable encode db) :
    Packed.erase encode (recover encode db h) = db := by
  unfold Recoverable at h
  funext name
  change (recover encode db h name).map (fun entry => encode entry.fst entry.snd) = db name
  cases found : db name with
  | none =>
    have recovered : recover encode db h name = none := Option.pmap_none' found
    rw [recovered]
    rfl
  | some observation =>
    have recovered : recover encode db h name = some (Classical.choose (h name observation found)) :=
      Option.pmap_some' found
    rw [recovered]
    exact congrArg some (Classical.choose_spec (h name observation found)).1

theorem recover_erase (db : Packed Name Tables) (h : Recoverable encode (Packed.erase encode db)) :
    recover encode (Packed.erase encode db) h = db := by
  unfold Recoverable at h
  funext name
  cases found : db name with
  | none =>
    have missing : Packed.erase encode db name = none := Option.map_eq_none_iff.mpr found
    exact Option.pmap_none' missing
  | some entry =>
    have observed : Packed.erase encode db name = some (encode entry.fst entry.snd) := by
      simp [Packed.erase, Partial.map, found]
    have recovered : recover encode (Packed.erase encode db) h name =
        some (Classical.choose (h name _ observed)) := Option.pmap_some' observed
    exact recovered.trans (congrArg some ((Classical.choose_spec (h name _ observed)).2 entry rfl).symm)

end Silmaril.Proofs.Relational.Database
