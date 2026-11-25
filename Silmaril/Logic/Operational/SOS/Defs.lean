module

public import Silmaril.Logic.Operational.Defs
public import Silmaril.Semantics.SOS.Thms

/-!
# Shapes and strict SOS presentations

A shape gives names to operational edges and may also have auxiliary judgments.
A strict map commutes with the edge naming function and sends each ground rule
to a rule in the target presentation.
-/

@[expose] public section

namespace Silmaril.Logic.Operational.SOS

open CategoryTheory Silmaril.Semantics.SOS Silmaril.Logic.Fragments
open Silmaril.Logic.Institution (Room)

universe u

/-- A labelled transition signature with a carrier of named judgments. -/
structure Shape extends Signature.{u} where
  Judgment : Type u
  edge : toSignature.Edge → Judgment

/-- A shape map respects the judgment name of every translated edge. -/
@[ext]
structure Shape.Hom (A B : Shape.{u}) where
  signature : A.toSignature ⟶ B.toSignature
  judgment : A.Judgment → B.Judgment
  map_edge : ∀ e, judgment (A.edge e) = B.edge (Signature.mapEdge signature e)

instance : Category.{u} Shape.{u} where
  Hom := Shape.Hom
  id _ := ⟨𝟙 _, id, fun _ => rfl⟩
  comp f g := ⟨f.signature ≫ g.signature, g.judgment ∘ f.judgment, fun e =>
    (congrArg g.judgment (f.map_edge e)).trans (g.map_edge _)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Forget auxiliary judgments and retain the operational carriers and maps. -/
def Shape.signatures : Shape.{u} ⥤ Signature.{u} where
  obj := Shape.toSignature
  map f := f.signature
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The atomic signature used for the judgment institution. -/
def Shape.atoms : Shape.{u} ⥤ AtomicSignature.{u} where
  obj A := ⟨A.Judgment⟩
  map f := ⟨f.judgment⟩
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev Shape.Model (A : Shape.{u}) := A.Judgment → Prop

/-- A reduct reads each source judgment at its translated target name. -/
def Shape.reduct {A B : Shape.{u}} (f : A ⟶ B) (M : B.Model) : A.Model :=
  M ∘ f.judgment

/-- Restrict a model to judgments named by labelled edges. -/
def Shape.edgeModel (A : Shape.{u}) (M : A.Model) : A.toSignature.Model :=
  M ∘ A.edge

/-- Ground rules over an SOS shape. The set can contain infinitely many instances. -/
structure Presentation where
  shape : Shape.{u}
  rules : Set (Rule shape.Judgment)

abbrev Presentation.Derives (P : Presentation.{u}) := Silmaril.Semantics.SOS.Derives P.rules

/-- A strict arrow sends each source rule to an actual target rule. -/
@[ext]
structure Presentation.Hom (P Q : Presentation.{u}) where
  shape : P.shape ⟶ Q.shape
  preserves : ∀ r ∈ P.rules, r.map shape.judgment ∈ Q.rules

instance : Category.{u} Presentation.{u} where
  Hom := Presentation.Hom
  id P := ⟨𝟙 P.shape, fun r hr => by
    change r.map id ∈ P.rules
    rwa [Rule.map_id]⟩
  comp f g := ⟨f.shape ≫ g.shape, fun r hr => by
    change r.map (g.shape.judgment ∘ f.shape.judgment) ∈ _
    rw [Rule.map_comp]
    exact g.preserves _ (f.preserves r hr)⟩
  id_comp f := Presentation.Hom.ext (Category.id_comp f.shape)
  comp_id f := Presentation.Hom.ext (Category.comp_id f.shape)
  assoc f g h := Presentation.Hom.ext (Category.assoc f.shape g.shape h.shape)

/-- Sentences assert a judgment or a finite implication between judgments. -/
inductive Sentence (J : Type u) where
  | atom : J → Sentence J
  | clause : Rule J → Sentence J

def Sentence.map {J K : Type u} (f : J → K) : Sentence J → Sentence K
  | .atom j => .atom (f j)
  | .clause r => .clause (r.map f)

def Sentence.Sat {J : Type u} (M : J → Prop) : Sentence J → Prop
  | .atom j => M j
  | .clause r => r.Holds M

@[simp] theorem Sentence.map_id {J : Type u} (φ : Sentence J) : φ.map id = φ := by
  cases φ with
  | atom _ => rfl
  | clause r => exact congrArg Sentence.clause r.map_id

theorem Sentence.map_comp {J K L : Type u} (f : J → K) (g : K → L) (φ : Sentence J) :
    φ.map (g ∘ f) = (φ.map f).map g := by
  cases φ with
  | atom _ => rfl
  | clause r => exact congrArg Sentence.clause (r.map_comp f g)

theorem Sentence.sat_map {J K : Type u} (f : J → K) (M : K → Prop) (φ : Sentence J) :
    (φ.map f).Sat M ↔ φ.Sat (M ∘ f) := by
  cases φ with
  | atom _ => rfl
  | clause r => exact r.holds_map f M

/-- Extend the atomic institution with finite clauses and reuse its model reducts. -/
def sentenceFragment : Fragment.{u} :=
  ⟨Sentence, Sentence.map, Sentence.Sat, Sentence.map_id, Sentence.map_comp, Sentence.sat_map⟩

/-- The institution of judgment atoms and finite clauses, with discrete predicate models. -/
def Shape.institution : Shape.{u} ⥤ Room.{u,u,u} :=
  Shape.atoms ⋙ sentenceFragment.atomic

/-- The component at one shape of the morphism from judgments to operational steps. -/
def Shape.edgeCorridor (A : Shape.{u}) : Signature.institution.obj A.toSignature ⟶
    Shape.institution.obj A :=
  ⟨fun e => .atom (A.edge e), Discrete.functor fun M => Discrete.mk (A.edgeModel M),
    fun _ _ => Iff.rfl⟩

/-- Regard the rules of a presentation as clause axioms in the judgment institution. -/
def Presentation.axioms (P : Presentation.{u}) : Set (Shape.institution.obj P.shape).Sen :=
  Sentence.clause '' P.rules

end Silmaril.Logic.Operational.SOS
