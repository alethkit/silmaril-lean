module

public import Silmaril.Logic.Fragments.Institution.Thms
public import Silmaril.Logic.Institution.Basic
public import Cslib.Foundations.Semantics.LTS.Relation

/-!
# Operational transition institutions

A signature fixes states and labels. A sentence names one labelled edge, and a
model is a predicate on edges. Signature maps send edge names forwards and pull
model predicates back. Systems over a presentation of signatures have a
separate category whose arrows explicitly preserve the edges of the models.
-/

@[expose] public section

namespace Silmaril.Logic.Operational

open CategoryTheory Silmaril.Logic.Fragments Silmaril.Logic.Institution

universe u v w

/-- The carriers of a labelled transition relation. -/
structure Signature where
  State : Type u
  Label : Type u

/-- State and label maps, both covariant. -/
@[ext]
structure Signature.Hom (A B : Signature.{u}) where
  state : A.State → B.State
  label : A.Label → B.Label

instance : Category.{u} Signature.{u} where
  Hom := Signature.Hom
  id _ := ⟨id, id⟩
  comp f g := ⟨g.state ∘ f.state, g.label ∘ f.label⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

namespace Signature

/-- A sentence names the source, label and target of a possible step. -/
abbrev Edge (S : Signature.{u}) := S.State × S.Label × S.State

/-- A model supplies the allowed edges of a labelled relation. -/
abbrev Model (S : Signature.{u}) := S.Edge → Prop

/-- Send a named edge forwards along a signature map. -/
def mapEdge {A B : Signature.{u}} (f : A ⟶ B) (e : A.Edge) : B.Edge :=
  (f.state e.1, f.label e.2.1, f.state e.2.2)

@[simp] theorem mapEdge_id (S : Signature.{u}) (e : S.Edge) :
    mapEdge (𝟙 S) e = e := rfl

@[simp] theorem mapEdge_comp {A B C : Signature.{u}} (f : A ⟶ B) (g : B ⟶ C) (e : A.Edge) :
    mapEdge (f ≫ g) e = mapEdge g (mapEdge f e) := rfl

/-- Pull back the target model's relation along a signature map. -/
def reduct {A B : Signature.{u}} (f : A ⟶ B) (M : B.Model) : A.Model :=
  M ∘ mapEdge f

/-- Edge names form the atoms of the existing predicate institution. -/
def atoms : Signature.{u} ⥤ AtomicSignature.{u} where
  obj S := ⟨S.Edge⟩
  map f := ⟨mapEdge f⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The institution of atomic labelled step claims. Model categories are discrete. -/
def institution : Signature.{u} ⥤ Room.{u,u,u} :=
  atoms ⋙ atomicInstitution

/-- The classic sentence/model functor presentation of the step institution. -/
def classic : ClassicInstitution Signature.{u} :=
  ClassicInstitution.ofRoomFunctor institution

/-- The operational satisfaction condition, in terms of edge predicates. -/
theorem satisfaction {A B : Signature.{u}} (f : A ⟶ B) (M : B.Model) (e : A.Edge) :
    M (mapEdge f e) ↔ reduct f M e := Iff.rfl

end Signature

/-- Read an edge predicate as the CSLib labelled transition system used by
Silmaril's operational execution and exploration APIs. -/
def Signature.toLTS {S : Signature.{u}} (M : S.Model) : Cslib.LTS S.State S.Label :=
  ⟨fun s l t => M (s, l, t)⟩

/-- Finite runs use CSLib's multi-step relation, with labels in execution order. -/
abbrev Runs {S : Signature.{u}} (M : S.Model) := (Signature.toLTS M).MTr

/-- A presented shape and one operational relation over its state and label carriers. -/
structure System {Shape : Type v} [Category.{w} Shape] (F : Shape ⥤ Signature.{u}) where
  shape : Shape
  model : (F.obj shape).Model

namespace System

variable {Shape : Type v} [Category.{w} Shape] {F : Shape ⥤ Signature.{u}}

/-- A forward simulation with a map in the chosen category of shapes. -/
@[ext]
structure Hom (A B : System F) where
  shape : A.shape ⟶ B.shape
  preserves : ∀ {e}, A.model e → B.model (Signature.mapEdge (F.map shape) e)

instance : Category.{w} (System F) where
  Hom := Hom
  id A := ⟨𝟙 A.shape, by
    intro e h
    rw [F.map_id, Signature.mapEdge_id]
    exact h⟩
  comp f g := ⟨f.shape ≫ g.shape, by
    intro e h
    rw [F.map_comp, Signature.mapEdge_comp]
    exact g.preserves (f.preserves h)⟩
  id_comp f := Hom.ext (Category.id_comp f.shape)
  comp_id f := Hom.ext (Category.comp_id f.shape)
  assoc f g h := Hom.ext (Category.assoc f.shape g.shape h.shape)

/-- Forget the relation and the preservation proof. -/
def forget : System F ⥤ Shape where
  obj A := A.shape
  map f := f.shape
  map_id _ := rfl
  map_comp _ _ := rfl

end System

/-- Operational systems with arbitrary state and label maps that preserve steps. -/
abbrev TransitionSystem := System (𝟭 Signature.{u})

end Silmaril.Logic.Operational
