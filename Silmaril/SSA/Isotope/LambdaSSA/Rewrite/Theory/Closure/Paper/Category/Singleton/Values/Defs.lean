module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Centrality.Thms

/-! # Pure return arrows in the Paper singleton category -/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory
open CfgEta.TypeCategory (returnRegion_typed)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {A B : τ} {a : Tm Φ}

local notation "Comp" => TypeCategory (τ := τ) Φ

/-- Bind the value of a typed expression before taking its single exit. -/
def returnTerm (h : Tm.HasType [A] a B) : ofType (Φ := Φ) A ⟶ ofType B :=
  ofRegion (returnRegion_typed h)

/-- The return of a primitive applied to its input. -/
def primitiveReturn (f : Φ) :
    ofType (Φ := Φ) (instrSrc (τ := τ) f) ⟶ ofType (instrTrg (τ := τ) f) :=
  returnTerm (a := .op f (.var 0)) (.op (.var rfl))

variable {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- The image of exactly typed pure expression returns in the computation quotient. -/
def PureReturn : MorphismProperty Comp :=
  fun A B f => ∃ (a : Tm Φ) (h : Tm.HasType [show τ from A] a (show τ from B)),
    Tm.Pure pe a ∧ f = returnTerm h

/-- Pure-return arrows equipped with both interchange squares. -/
def CentralPureReturn : MorphismProperty Comp :=
  fun _ _ f => PureReturn pe f ∧ WhiskerCentral f

/-- Each primitive marked pure must satisfy both squares against arbitrary computations. -/
def PrimitiveReturnsCentral : Prop :=
  ∀ f : Φ, IsPure pe f → WhiskerCentral (primitiveReturn (τ := τ) f)

/-- The two kinds of generators for sequential composition of pure returns. -/
def PureReturnGenerators : MorphismProperty Comp :=
  fun A B f =>
    (∃ (a : Tm Φ) (h : Tm.BranchValue [show τ from A] a (show τ from B)), f = returnTerm h.hasType) ∨
    (∃ (p : Φ) (h : Tm.HasType [show τ from A] (.op p (.var 0)) (show τ from B)),
      IsPure pe p ∧ f = returnTerm h)

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
