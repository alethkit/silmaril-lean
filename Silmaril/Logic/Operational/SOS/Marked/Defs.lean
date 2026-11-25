module

public import Silmaril.Logic.Operational.SOS.Thms
public import Silmaril.Semantics.Operational.Program.Defs

/-!
# SOS with a distinguished UB judgment

The ordinary tags name labelled transitions, entries and endpoints. The marked
language adds a state-indexed tag. Both use the same carrier maps, which act
on each tag's fields. Interpreted maps preserve judgment truth, including truth
of the marker in the marked language. The marker alone adds no transitions or
outcomes.
-/

@[expose] public section

namespace Silmaril.Logic.Operational.SOS.Marked

open CategoryTheory Silmaril.Logic.Fragments Silmaril.Semantics.SOS
open Silmaril.Semantics.Operational (Outcome)

universe u

/-- Common carriers of ordinary and marked signatures. Endpoints use the finite
policy outcomes, including a distinct trap tag. -/
structure Carriers extends Signature.{u} where
  Program : Type u
  Observation : Type u

@[ext]
structure Carriers.Hom (A B : Carriers.{u}) where
  signature : A.toSignature ⟶ B.toSignature
  program : A.Program → B.Program
  observation : A.Observation → B.Observation

instance : Category.{u} Carriers.{u} where
  Hom := Carriers.Hom
  id _ := ⟨𝟙 _, id, id⟩
  comp f g := ⟨f.signature ≫ g.signature, g.program ∘ f.program, g.observation ∘ f.observation⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Tags are freely generated with disjoint constructors. -/
inductive Judgment (A : Carriers.{u}) where
  | step : A.toSignature.Edge → Judgment A
  | entry : A.Program → A.State → Judgment A
  | endpoint : A.State → Outcome A.Observation → Judgment A

/-- The right summand names UB at a state. -/
abbrev MarkedJudgment (A : Carriers.{u}) := Judgment A ⊕ A.State

def Carriers.Hom.judgment {A B : Carriers.{u}} (f : A ⟶ B) : Judgment A → Judgment B
  | .step e => .step (Signature.mapEdge f.signature e)
  | .entry p s => .entry (f.program p) (f.signature.state s)
  | .endpoint s o => .endpoint (f.signature.state s) (o.map f.observation)

def Carriers.Hom.markedJudgment {A B : Carriers.{u}} (f : A ⟶ B) :
    MarkedJudgment A → MarkedJudgment B :=
  Sum.map f.judgment f.signature.state

/-- The ordinary names are the left summand of the marked names. -/
def includeJudgment {A : Carriers.{u}} : Judgment A → MarkedJudgment A := Sum.inl

/-- The name of the distinguished UB judgment. -/
def ubJudgment {A : Carriers.{u}} : A.State → MarkedJudgment A := Sum.inr

def Carriers.ordinaryShape (A : Carriers.{u}) : Shape.{u} :=
  ⟨A.toSignature, Judgment A, Judgment.step⟩

def Carriers.markedShape (A : Carriers.{u}) : Shape.{u} :=
  ⟨A.toSignature, MarkedJudgment A, includeJudgment ∘ Judgment.step⟩

/-- Interpret only the ordinary tags of the target predicate. -/
def forgetPredicate {A : Carriers.{u}} (M : MarkedJudgment A → Prop) : Judgment A → Prop :=
  M ∘ includeJudgment

/-- Extend the predicate by setting every UB atom to false. -/
def emptyPredicate {A : Carriers.{u}} (M : Judgment A → Prop) : MarkedJudgment A → Prop
  | .inl j => M j
  | .inr _ => False

/-- The category of predicates over SOS shapes carried by `Carriers`, with
forward truth-preserving maps. Institution model categories remain discrete. -/
structure Interpretation (F : Carriers.{u} ⥤ Shape.{u}) where
  carriers : Carriers.{u}
  model : (F.obj carriers).Model

namespace Interpretation

variable {F : Carriers.{u} ⥤ Shape.{u}}

@[ext]
structure Hom (M N : Interpretation F) where
  carriers : M.carriers ⟶ N.carriers
  preserves : ∀ j, M.model j → N.model ((F.map carriers).judgment j)

instance : Category.{u} (Interpretation F) where
  Hom := Hom
  id M := ⟨𝟙 M.carriers, by
    intro j h
    rw [F.map_id]
    exact h⟩
  comp f g := ⟨f.carriers ≫ g.carriers, by
    intro j h
    rw [F.map_comp]
    exact g.preserves _ (f.preserves _ h)⟩
  id_comp f := Hom.ext (Category.id_comp f.carriers)
  comp_id f := Hom.ext (Category.comp_id f.carriers)
  assoc f g h := Hom.ext (Category.assoc f.carriers g.carriers h.carriers)

/-- The labelled relation supplied by the edge tags, with the original carriers. -/
def system (M : Interpretation F) : System (F ⋙ Shape.signatures) :=
  ⟨M.carriers, (F.obj M.carriers).edgeModel M.model⟩

def Hom.toSystem {M N : Interpretation F} (f : M ⟶ N) : M.system ⟶ N.system :=
  ⟨f.carriers, fun {e} h =>
    show N.model ((F.obj N.carriers).edge (Signature.mapEdge (F.map f.carriers).signature e))
      from (F.map f.carriers).map_edge e ▸ f.preserves _ h⟩

/-- Forward truth preservation maps raw labelled steps and hence finite runs. -/
def toSystems (F : Carriers.{u} ⥤ Shape.{u}) : Interpretation F ⥤ System (F ⋙ Shape.signatures) where
  obj := system
  map := Hom.toSystem
  map_id _ := System.Hom.ext rfl
  map_comp _ _ := System.Hom.ext rfl

end Interpretation

/-- Use the library's strict syntactic presentation category on clause syntax.
Axioms are exactly the positive ground rules, including zero-premise facts. -/
def ruleFragment : Fragment.{u} :=
  ⟨Rule, Rule.map, Rule.Holds, Rule.map_id, Rule.map_comp, Rule.holds_map⟩

abbrev RulePresentation (F : Carriers.{u} ⥤ Shape.{u}) :=
  Silmaril.Logic.Institution.Presentation (F ⋙ Shape.atoms ⋙ ruleFragment.atomic)

namespace RulePresentation

/-- Read a tagged rule presentation in the generic SOS presentation category. -/
def toSOS (F : Carriers.{u} ⥤ Shape.{u}) : RulePresentation F ⥤ SOS.Presentation.{u} where
  obj P := ⟨F.obj P.sig, P.axioms⟩
  map f := ⟨F.map f.sig, fun r hr => f.mapsTo (x := r) hr⟩
  map_id P := SOS.Presentation.Hom.ext (F.map_id P.sig)
  map_comp f g := SOS.Presentation.Hom.ext (F.map_comp f.sig g.sig)

/-- Interpret every judgment by derivability from the supplied rules. -/
def interpret (F : Carriers.{u} ⥤ Shape.{u}) : RulePresentation F ⥤ Interpretation F where
  obj P := ⟨P.sig, ((toSOS F).obj P).Derives⟩
  map f := ⟨f.sig, fun j h => SOS.Presentation.Hom.derives ((toSOS F).map f) (j := j) h⟩
  map_id _ := Interpretation.Hom.ext rfl
  map_comp _ _ := Interpretation.Hom.ext rfl

end RulePresentation

end Silmaril.Logic.Operational.SOS.Marked
