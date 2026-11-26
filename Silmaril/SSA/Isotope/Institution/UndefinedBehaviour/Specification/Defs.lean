module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.Thms

/-! # Adjoining the top inequations to an ordered specification -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Institution.Refinement.UB

open CategoryTheory
open Silmaril.Logic.Metatheory.TheoryModel
open Silmaril.Logic.Institution

universe u v

set_option linter.checkUnivs false in
/-- Ordered specifications with morphisms preserving axioms up to semantic consequence. -/
abbrev Specification := Spec (institution.{u,v,max u v})

namespace Specification

/-- All inequations putting a chosen constant above the syntax at its judgment sort. -/
def below (P : PSig.{u,v,max u v}) (c : (i : P.Index) → Nullary P.sig i) :
    Set (Sentence P) :=
  {s | ∃ (i : P.Index) (t : P.syn.Carrier i), s = [⟨i, t, constant P (c i)⟩]}

/-- The designated fresh operation at every sort of the extension. -/
def fresh (P : PSig.{u,v,max u v}) (i : (adjoin P).Index) : Nullary (adjoin P).sig i :=
  ⟨none, rfl⟩

/-- Extend the signature, transport the old axioms, and add all top comparisons. -/
def free (P : Specification.{u,v}) : Specification.{u,v} where
  sig := adjoin P.sig
  axioms := Sentence.map (inclusion P.sig) '' P.axioms ∪ below (adjoin P.sig) (fresh P.sig)

/-- A chosen family is top among denotations of well-sorted terms in the specification. -/
def IsTop (Q : Specification.{u,v}) (c : (i : Q.sig.Index) → Nullary Q.sig.sig i) : Prop :=
  below Q.sig c ⊆ (institution.obj Q.sig).closure Q.axioms

/-- Inclusion of the original specification. -/
def unit (P : Specification.{u,v}) : P ⟶ free P where
  sig := inclusion P.sig
  mapsTo := fun s hs => (institution.obj (free P).sig).subset_closure (free P).axioms
    (Or.inl ⟨s, hs, rfl⟩)

/-- Semantic closure of the extended axioms, viewed as a compatible preorder on syntax. -/
def freeOrder (P : UB.Specification.{u,v}) : CompatiblePreorder (free P).sig.syn :=
  preorderOf ((Spec.closure institution).obj (free P))

/-- The antisymmetrized syntax of the extended specification. -/
def syntacticModel (P : UB.Specification.{u,v}) :
    OrderedModels (free P).sig.isInitial (freeOrder P) :=
  orderedQuotientModel _ _

/-- The class of the fresh constant in the initial ordered model. -/
def ubClass (P : UB.Specification.{u,v}) (i : (free P).sig.Index) :
    (syntacticModel P).algebra.Carrier i :=
  (quotientMap (freeOrder P).equationalCore).map (Expr.ub (i := i))

end Specification
end Silmaril.Isotope.Institution.Refinement.UB
