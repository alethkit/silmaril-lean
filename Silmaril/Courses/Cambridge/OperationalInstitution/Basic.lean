module

public import Silmaril.Logic.Operational.Thms
public import Silmaril.Semantics.Operational.Policy.Defs

/-! A shared entry point for reading a course's existing CSLib LTS in the
operational transition institution, with a finite outcome view for unit labels. -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.OperationalInstitution

open CategoryTheory Silmaril.Logic.Operational Silmaril.Semantics.Operational

universe u

variable {State Label : Type u}

/-- Use the LTS carriers and edge predicate verbatim. -/
def ofLTS (lts : Cslib.LTS State Label) : TransitionSystem.{u} :=
  ⟨⟨State, Label⟩, fun (s, a, t) => lts.Tr s a t⟩

@[simp] theorem toLTS_ofLTS (lts : Cslib.LTS State Label) :
    Signature.toLTS (ofLTS lts).model = lts := by
  cases lts
  rfl

/-- Satisfaction in the operational room reads the original labelled step. -/
theorem sat_iff (lts : Cslib.LTS State Label) (s t : State) (a : Label) :
    (Signature.institution.obj (ofLTS lts).shape).Sat (Discrete.mk (ofLTS lts).model)
      (s, a, t) ↔ lts.Tr s a t :=
  Iff.rfl

/-- Taking the reduct of the LTS model along a signature map tests the original transition
relation on the translated endpoints and label. -/
theorem model_reduct (lts : Cslib.LTS State Label) {A : Signature.{u}}
    (f : A ⟶ (ofLTS lts).shape) :
    (Signature.institution.map f).mod.obj (Discrete.mk (ofLTS lts).model) =
      Discrete.mk (Signature.reduct f (ofLTS lts).model) :=
  rfl

/-- Read the unit-labelled step relation with a course-supplied value test.
A return reports the full value configuration. -/
def valueSemantics {State : Type} (lts : Cslib.LTS State Unit) (isValue : State → Prop) :
    OpSem State State where
  step s t := (ofLTS lts).model (s, (), t)
  observe s result := isValue s ∧ result = .returned s

theorem may_return_iff {State : Type} (lts : Cslib.LTS State Unit) (isValue : State → Prop)
    (s t : State) :
    (valueSemantics lts isValue).May s (.returned t) ↔
      Relation.ReflTransGen (fun s t => lts.Tr s () t) s t ∧ isValue t := by
  constructor
  · rintro ⟨target, path, value, equal⟩
    cases equal
    exact ⟨path, value⟩
  · rintro ⟨path, value⟩
    exact ⟨t, path, value, rfl⟩

end Silmaril.Courses.Cambridge.OperationalInstitution
