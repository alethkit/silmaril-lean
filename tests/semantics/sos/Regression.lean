module

import Silmaril.Logic.Operational.SOS.Thms
import Silmaril.Logic.Operational.Thms

open CategoryTheory Silmaril.Logic.Operational Silmaril.Logic.Operational.SOS
open Silmaril.Semantics.SOS

private inductive Judgment where
  | edge (source : Nat) (label : Bool) (target : Nat)
  | enabled (state : Nat)

private abbrev counterShape : Shape :=
  ⟨⟨Nat, Bool⟩, Judgment, fun (s, b, t) => .edge s b t⟩

private def fact (n : Nat) : Rule Judgment :=
  ⟨[], .enabled n⟩

private def advance (n : Nat) (b : Bool) : Rule Judgment :=
  ⟨[.enabled n, .enabled (n + 1)], .edge n b (n + 1)⟩

private def rules (enabled : Nat → Prop) : Set (Rule Judgment) :=
  {r | (∃ n, enabled n ∧ r = fact n) ∨ ∃ n b, r = advance n b}

private def counter : Presentation :=
  ⟨counterShape, rules (fun _ => True)⟩

private def model (enabled : Nat → Prop) : Judgment → Prop
  | .enabled n => enabled n
  | .edge s _ t => t = s + 1 ∧ enabled s ∧ enabled t

private theorem modelClosed (enabled : Nat → Prop) : Closed (rules enabled) (model enabled) := by
  rintro r (⟨n, hn, rfl⟩ | ⟨n, b, rfl⟩) h
  · exact hn
  · exact ⟨rfl, h (.enabled n) (by simp [advance]), h (.enabled (n + 1)) (by simp [advance])⟩

private theorem enabledFact (n : Nat) : counter.Derives (.enabled n) :=
  .apply (r := fact n) (Or.inl ⟨n, trivial, rfl⟩) (fun _ h => nomatch h)

private theorem step (n : Nat) (b : Bool) : counter.system.model (n, b, n + 1) :=
  Derives.apply (r := advance n b) (Or.inr ⟨n, b, rfl⟩) fun j hj => by
    simp only [advance, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact enabledFact n
    · exact enabledFact (n + 1)

-- Recover an independent edge specification and reject an edge with a missing premise.
example (s : Nat) (b : Bool) (t : Nat) : counter.system.model (s, b, t) ↔ t = s + 1 := by
  constructor
  · intro h
    have h' : counter.Derives (.edge s b t) := h
    exact (h'.least (modelClosed _)).1
  · rintro rfl
    exact step s b

example : ¬ Derives (rules (fun n => n = 0)) (.edge 0 true 1) :=
  fun h => Nat.one_ne_zero (h.least (modelClosed _)).2.2

private def rename (label : Bool → Bool) : counterShape ⟶ counterShape where
  signature := ⟨Nat.succ, label⟩
  judgment
    | .enabled n => .enabled n.succ
    | .edge s b t => .edge s.succ (label b) t.succ
  map_edge _ := rfl

private def shift : counter ⟶ counter where
  shape := rename Bool.not
  preserves := by
    rintro r (⟨n, _, rfl⟩ | ⟨n, b, rfl⟩)
    · exact Or.inl ⟨n.succ, trivial, rfl⟩
    · exact Or.inr ⟨n.succ, !b, rfl⟩

example : counter.Derives (.enabled 2) :=
  Presentation.Hom.derives (shift ≫ shift) (enabledFact 0)

private abbrev transitions := Presentation.toTransitionSystems.obj counter

private theorem twoSteps : Runs transitions.model (0 : Nat) [true, false] (2 : Nat) :=
  .stepL (step 0 true) (.stepL (step 1 false) .refl)

example : Runs transitions.model (1 : Nat) [false, true] (3 : Nat) :=
  System.Hom.runs (Presentation.toTransitionSystems.map shift) twoSteps

example : Runs transitions.model (2 : Nat) [true, false] (4 : Nat) :=
  System.Hom.runs (Presentation.toTransitionSystems.map (shift ≫ shift)) twoSteps

example :
    Presentation.toSystems.map (shift ≫ shift) =
      Presentation.toSystems.map shift ≫ Presentation.toSystems.map shift :=
  Presentation.toSystems.map_comp shift shift

example :
    Presentation.toTransitionSystems.map (𝟙 counter) = 𝟙 transitions :=
  Presentation.toTransitionSystems.map_id counter

private abbrev room := Shape.institution.obj counterShape

-- Both edge premises coalesce after renaming the labels to true.
private def clause : room.Sen :=
  .clause ⟨[.edge 0 true 1, .edge 0 false 1], .enabled 1⟩

example (M : counterShape.Model) :
    room.Sat (Discrete.mk M) ((Shape.institution.map (rename fun _ => true)).sen clause) ↔
      room.Sat (Discrete.mk (Shape.reduct (rename fun _ => true) M)) clause :=
  (Shape.institution.map (rename fun _ => true)).sat (Discrete.mk M) clause

example (M : counterShape.Model) (e : counterShape.toSignature.Edge) :
    room.Sat (Discrete.mk M) (Sentence.atom (counterShape.edge e)) ↔
      counterShape.edgeModel M e :=
  (counterShape.edgeCorridor).sat (Discrete.mk M) e

example :
    (Shape.signatures ⋙ Signature.institution).map (rename Bool.not) ≫ counterShape.edgeCorridor =
      counterShape.edgeCorridor ≫ Shape.institution.map (rename Bool.not) :=
  Shape.toOperational.η.naturality (rename Bool.not)

example : Discrete.mk counter.Derives ∈ room.modelsOf counter.axioms :=
  counter.derives_models

-- A valid strict map can land in a presentation with new derivations.
private def empty : Presentation := ⟨counterShape, ∅⟩

private def includeEmpty : empty ⟶ counter :=
  ⟨𝟙 counterShape, fun _ h => False.elim h⟩

example :
    Shape.reduct includeEmpty.shape counter.Derives (.enabled 0) ∧
      ¬ empty.Derives (.enabled 0) :=
  ⟨enabledFact 0, fun h => h.least (M := fun _ => False) (fun _ hr => False.elim hr)⟩
