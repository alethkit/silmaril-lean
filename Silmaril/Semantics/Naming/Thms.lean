module

public import Silmaril.Semantics.Naming.Defs
import Silmaril.Proofs.Semantics.Naming.Basic

public section

namespace Silmaril.Semantics.Naming

variable {Name Payload Wire : Type} {rel other : Relation Name Payload}

theorem fillMissing_binding (base : Binding rel) (defaults : Binding other) :
    Binding (fillMissing rel other) := Proofs.Semantics.Naming.fillMissing_binding base defaults

theorem subset_fillMissing : Subset rel (fillMissing rel other) := fun _ _ hit => .inl hit

theorem Binding.subset (bound : Binding rel) (incl : Subset other rel) : Binding other := by
  intro name left right first second
  exact bound (incl first) (incl second)

theorem Binding.inter (bound : Binding rel) : Binding (inter rel other) :=
  bound.subset (by intro name payload member; exact member.1)

theorem binding_iff_no_collisions : Binding rel ↔ collisions rel = ∅ :=
  Proofs.Semantics.Naming.binding_iff_no_collisions

theorem graph_binding (read : Name → Option Payload) : Binding (graph read) := by
  intro name left right first second
  exact Option.some.inj (first.symm.trans second)

@[simp] theorem Binding.lookup_eq_some (bound : Binding rel) {name payload} :
    bound.lookup name = some payload ↔ rel name payload :=
  Proofs.Semantics.Naming.lookup_eq_some bound

@[simp] theorem UniqueNames.lookup_eq_some (unique : UniqueNames rel) {name payload} :
    unique.lookup payload = some name ↔ rel name payload := Binding.lookup_eq_some unique

theorem Binding.push (bound : Binding rel) {serializes : Payload → Wire → Prop}
    (deterministic : Binding serializes) : Binding (push rel serializes) :=
  Proofs.Semantics.Naming.push_binding bound deterministic

/-- A functional parser recovers the particular source of a serialized byte string. -/
theorem push_parse_iff {serializes : Payload → Wire → Prop} {parse : Wire → Option Payload}
    (recovers : ∀ ⦃payload wire⦄, serializes payload wire → parse wire = some payload)
    {name wire payload} (parsed : parse wire = some payload) :
    push rel serializes name wire ↔ rel name payload ∧ serializes payload wire :=
  Proofs.Semantics.Naming.push_parse_iff recovers parsed

theorem HashCompatible.uniqueNames {hash : Wire → Name} {bytes : Relation Name Wire}
    (integrity : HashCompatible hash bytes) : UniqueNames bytes := by
  intro wire left right first second
  exact (integrity first).symm.trans (integrity second)

theorem UniqueNames.of_push {serializes : Payload → Wire → Prop}
    (unique : UniqueNames (push rel serializes)) (total : ∀ payload, ∃ wire, serializes payload wire) :
    UniqueNames rel := by
  intro payload left right first second
  obtain ⟨wire, encoded⟩ := total payload
  exact unique ⟨payload, first, encoded⟩ ⟨payload, second, encoded⟩

theorem Stores.Binding.subset {Obj Blob : Type} {left right : Stores Name Obj Blob}
    (bound : right.Binding) (incl : left.Subset right) : left.Binding :=
  ⟨bound.1.subset incl.1, bound.2.subset incl.2⟩

theorem Stores.Binding.flatten {Obj : Type} {store : Stores Name Obj Wire} (bound : store.Binding)
    (disjoint : store.DisjointDomains) {serializes : Obj → Wire → Prop}
    (deterministic : Naming.Binding serializes) : Naming.Binding (store.flatten serializes) :=
  Proofs.Semantics.Naming.flatten_binding bound disjoint deterministic

theorem Checked.classify_merge (left right : Relation Name Payload) :
    (classify left).merge (classify right) = classify (union left right) :=
  Proofs.Semantics.Naming.classify_merge left right

theorem Checked.merge_assoc (left mid right : Checked Name Payload) :
    (left.merge mid).merge right = left.merge (mid.merge right) :=
  Proofs.Semantics.Naming.merge_assoc left mid right

theorem Checked.merge_comm (left right : Checked Name Payload) : left.merge right = right.merge left :=
  Proofs.Semantics.Naming.merge_comm left right

@[simp] theorem Checked.merge_idem (snapshot : Checked Name Payload) : snapshot.merge snapshot = snapshot :=
  Proofs.Semantics.Naming.merge_idem snapshot

end Silmaril.Semantics.Naming
