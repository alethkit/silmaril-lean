module

public import Silmaril.Logic.Operational.SOS.Marked.Defs
import Silmaril.Proofs.Logic.Operational.SOS.Marked.Shapes

@[expose] public section

namespace Silmaril.Logic.Operational.SOS.Marked

open CategoryTheory Silmaril.Logic.Fragments
open Silmaril.Logic.Institution (Room Corridor Inst)

universe u

@[simp] theorem Carriers.Hom.judgment_id (A : Carriers.{u}) (j : Judgment A) :
    judgment (𝟙 A) j = j :=
  Proofs.judgment_id A j

theorem Carriers.Hom.judgment_comp {A B C : Carriers.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (j : Judgment A) : judgment (f ≫ g) j = g.judgment (f.judgment j) :=
  Proofs.judgment_comp f g j

/-- The ordinary shape functor maps every primitive tag componentwise. -/
def ordinaryShapes : Carriers.{u} ⥤ Shape.{u} where
  obj := Carriers.ordinaryShape
  map f := ⟨f.signature, f.judgment, fun _ => rfl⟩
  map_id A := Shape.Hom.ext rfl (funext (Carriers.Hom.judgment_id A))
  map_comp f g := Shape.Hom.ext rfl (funext (Carriers.Hom.judgment_comp f g))

/-- The marked shape functor additionally maps the UB name along the state map. -/
def markedShapes : Carriers.{u} ⥤ Shape.{u} where
  obj := Carriers.markedShape
  map f := ⟨f.signature, f.markedJudgment, fun _ => rfl⟩
  map_id A := Shape.Hom.ext rfl <| funext fun
    | .inl j => congrArg Sum.inl (Carriers.Hom.judgment_id A j)
    | .inr _ => rfl
  map_comp f g := Shape.Hom.ext rfl <| funext fun
    | .inl j => congrArg Sum.inl (Carriers.Hom.judgment_comp f g j)
    | .inr _ => rfl

abbrev Ordinary := Interpretation ordinaryShapes.{u}
abbrev WithMarker := Interpretation markedShapes.{u}
abbrev OrdinaryRules := RulePresentation ordinaryShapes.{u}
abbrev MarkedRules := RulePresentation markedShapes.{u}

/-- Forget the UB predicate of an interpreted model. The ordinary predicates,
including conclusions supported by UB premises in some presentation, are retained. -/
def forget : WithMarker.{u} ⥤ Ordinary.{u} where
  obj M := ⟨M.carriers, forgetPredicate M.model⟩
  map f := ⟨f.carriers, fun j h => f.preserves (includeJudgment j) h⟩
  map_id _ := Interpretation.Hom.ext rfl
  map_comp _ _ := Interpretation.Hom.ext rfl

/-- Extend an interpreted model by the empty UB predicate. -/
def emptyMarker : Ordinary.{u} ⥤ WithMarker.{u} where
  obj M := ⟨M.carriers, emptyPredicate M.model⟩
  map f := ⟨f.carriers, fun
    | .inl j => f.preserves j
    | .inr _ => False.elim⟩
  map_id _ := Interpretation.Hom.ext rfl
  map_comp _ _ := Interpretation.Hom.ext rfl

@[simp] theorem emptyMarker_forget : emptyMarker.{u} ⋙ forget = 𝟭 Ordinary.{u} := rfl

def emptyMarkerFullyFaithful : (emptyMarker.{u}).FullyFaithful where
  preimage f := forget.map f
  map_preimage _ := Interpretation.Hom.ext rfl
  preimage_map _ := Interpretation.Hom.ext rfl

instance : (forget.{u}).Faithful where
  map_injective {X Y} _ _ h := Interpretation.Hom.ext
    (congrArg (fun f : forget.obj X ⟶ forget.obj Y => f.carriers) h)

/-- The two tagged shape functors have the same underlying operational signatures. -/
theorem forget_toSystems :
    forget.{u} ⋙ Interpretation.toSystems ordinaryShapes =
      Interpretation.toSystems markedShapes := rfl

/-- Preservation of the empty UB predicate is automatic, so both hom types
are determined by the same truth-preserving carrier maps. -/
def emptyMarkerHomEquiv (M : Ordinary.{u}) (N : WithMarker.{u}) :
    (emptyMarker.obj M ⟶ N) ≃ (M ⟶ forget.obj N) where
  toFun f := ⟨f.carriers, fun j h => f.preserves (includeJudgment j) h⟩
  invFun f := ⟨f.carriers, fun
    | .inl j => f.preserves j
    | .inr _ => False.elim⟩
  left_inv _ := Interpretation.Hom.ext rfl
  right_inv _ := Interpretation.Hom.ext rfl

/-- Empty-marker extension is left adjoint to interpreted forgetting. -/
def emptyMarkerAdjunction : emptyMarker.{u} ⊣ forget :=
  Adjunction.mkOfHomEquiv
    { homEquiv := emptyMarkerHomEquiv
      homEquiv_naturality_left_symm _ _ := Interpretation.Hom.ext rfl
      homEquiv_naturality_right _ _ := Interpretation.Hom.ext rfl }

/-- The inclusion of ordinary atoms commutes with all componentwise carrier maps. -/
def includeAtoms : ordinaryShapes.{u} ⋙ Shape.atoms ⟶ markedShapes.{u} ⋙ Shape.atoms where
  app _ := ⟨includeJudgment⟩
  naturality _ _ _ := rfl

/-- Ordinary judgment atoms and clauses. -/
def ordinaryInstitution : Carriers.{u} ⥤ Room.{u,u,u} :=
  ordinaryShapes ⋙ Shape.institution

/-- The same sentence fragment over the marked judgment names. -/
def markedInstitution : Carriers.{u} ⥤ Room.{u,u,u} :=
  markedShapes ⋙ Shape.institution

/-- Include ordinary names in sentences and restrict model predicates to those names. -/
def includeSentences : ordinaryInstitution.{u} ⟶ markedInstitution.{u} :=
  CategoryTheory.Functor.whiskerRight includeAtoms sentenceFragment.atomic

def ordinaryInst : Inst.{u+1,u,u,u,u} := ⟨Carriers, ordinaryInstitution⟩
def markedInst : Inst.{u+1,u,u,u,u} := ⟨Carriers, markedInstitution⟩

/-- Ordinary sentences retain their truth in marked models under predicate restriction. -/
def toMarked : Inst.CoHom ordinaryInst.{u} markedInst.{u} :=
  ⟨𝟭 _, includeSentences ≫ (CategoryTheory.Functor.leftUnitor markedInstitution).inv⟩

/-- The marked-to-ordinary morphism uses the same predicate restriction and
interprets each ordinary sentence in the marked language. -/
def toOrdinary : Inst.Hom markedInst.{u} ordinaryInst.{u} :=
  ⟨𝟭 _, (CategoryTheory.Functor.leftUnitor ordinaryInstitution).hom ≫ includeSentences⟩

theorem satisfaction_include {A : Carriers.{u}} (M : MarkedJudgment A → Prop)
    (φ : Sentence (Judgment A)) :
    (φ.map includeJudgment).Sat M ↔ φ.Sat (forgetPredicate M) :=
  φ.sat_map includeJudgment M

/-- Every ordinary model expands by interpreting all UB atoms as false. -/
theorem includeSentences_modelExpansive (A : Carriers.{u}) :
    (includeSentences.app A).ModelExpansive :=
  fun M => ⟨Discrete.mk (emptyPredicate M.as), rfl⟩

end Silmaril.Logic.Operational.SOS.Marked
