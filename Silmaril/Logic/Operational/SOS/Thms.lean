module

public import Silmaril.Logic.Operational.SOS.Defs
public import Silmaril.Logic.Institution.Morphism
import Silmaril.Proofs.Logic.Operational.SOS.Institution

@[expose] public section

namespace Silmaril.Logic.Operational.SOS

open CategoryTheory Silmaril.Semantics.SOS
open Silmaril.Logic.Institution (Room ClassicInstitution Inst)

universe u

@[simp] theorem Shape.reduct_id (A : Shape.{u}) (M : A.Model) :
    reduct (𝟙 A) M = M := rfl

@[simp] theorem Shape.reduct_comp {A B C : Shape.{u}} (f : A ⟶ B) (g : B ⟶ C) (M : C.Model) :
    reduct (f ≫ g) M = reduct f (reduct g M) := rfl

/-- Renaming sentences and pulling predicates back preserve and reflect satisfaction. -/
theorem Shape.sat_map {A B : Shape.{u}} (f : A ⟶ B) (M : B.Model) (φ : Sentence A.Judgment) :
    (φ.map f.judgment).Sat M ↔ φ.Sat (reduct f M) :=
  φ.sat_map f.judgment M

/-- The classic sentence and model functors of the judgment institution. -/
def Shape.classic : ClassicInstitution Shape.{u} :=
  ClassicInstitution.ofRoomFunctor Shape.institution

theorem Shape.edge_naturality {A B : Shape.{u}} (f : A ⟶ B) :
    (Shape.signatures ⋙ Signature.institution).map f ≫ B.edgeCorridor =
      A.edgeCorridor ≫ Shape.institution.map f :=
  Proofs.edge_naturality f

/-- The institution morphism interprets operational edges as SOS atoms.
Its model map restricts a judgment predicate to those atoms. -/
def Shape.toOperational :
    Inst.Hom (⟨Shape.{u}, Shape.institution⟩ : Inst.{u+1,u,u,u,u})
      (⟨Signature.{u}, Signature.institution⟩ : Inst.{u+1,u,u,u,u}) :=
  ⟨Shape.signatures, ⟨Shape.edgeCorridor, fun _ _ f => Shape.edge_naturality f⟩⟩

theorem Presentation.models_iff_closed (P : Presentation.{u}) (M : P.shape.Model) :
    Discrete.mk M ∈ (Shape.institution.obj P.shape).modelsOf P.axioms ↔ Closed P.rules M :=
  Proofs.models_iff_closed P M

/-- The derivability predicate satisfies the clause axioms. Every other model
of the axioms contains it, by `Derives.least`. -/
theorem Presentation.derives_models (P : Presentation.{u}) :
    Discrete.mk P.Derives ∈ (Shape.institution.obj P.shape).modelsOf P.axioms :=
  (P.models_iff_closed P.Derives).mpr (derives_closed P.rules)

/-- Strict rule maps preserve every derivable judgment. -/
theorem Presentation.Hom.derives {P Q : Presentation.{u}} (f : P ⟶ Q) {j : P.shape.Judgment}
    (h : P.Derives j) : Q.Derives (f.shape.judgment j) :=
  Derives.map f.shape.judgment f.preserves h

/-- The operational system of derivable edges, retaining its SOS shape. -/
def Presentation.system (P : Presentation.{u}) : System Shape.signatures :=
  ⟨P.shape, P.shape.edgeModel P.Derives⟩

/-- Derivability preservation gives step preservation along the same shape map. -/
def Presentation.Hom.toSystem {P Q : Presentation.{u}} (f : P ⟶ Q) : P.system ⟶ Q.system :=
  ⟨f.shape, fun {e} h =>
    show Q.Derives (Q.shape.edge (Signature.mapEdge f.shape.signature e)) from
      f.shape.map_edge e ▸ f.derives h⟩

/-- Interpret a strict SOS presentation as an operational system. -/
def Presentation.toSystems : Presentation.{u} ⥤ System Shape.signatures where
  obj := Presentation.system
  map := Presentation.Hom.toSystem
  map_id _ := System.Hom.ext rfl
  map_comp _ _ := System.Hom.ext rfl

/-- Retain just the operational carriers and edge predicates of SOS-shaped systems. -/
def Shape.toTransitionSystems : System Shape.signatures.{u} ⥤ TransitionSystem.{u} where
  obj A := ⟨A.shape.toSignature, A.model⟩
  map f := ⟨f.shape.signature, f.preserves⟩
  map_id _ := System.Hom.ext rfl
  map_comp _ _ := System.Hom.ext rfl

/-- Interpret a strict SOS presentation as a labelled transition system. -/
def Presentation.toTransitionSystems : Presentation.{u} ⥤ TransitionSystem.{u} :=
  Presentation.toSystems ⋙ Shape.toTransitionSystems

end Silmaril.Logic.Operational.SOS
