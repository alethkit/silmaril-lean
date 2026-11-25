module

public import Silmaril.SSA.RVSDG.LambdaSSA.Theta.Defs
public import Silmaril.SSA.RVSDG.Theta.Categorical.Defs

/-! # Common pure step and boundary maps for the two loop interpretations -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Theta

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical (ctxObj)

universe u v d h
variable {τ : Type u} {Φ : Type v} [TypeFormers τ] [HasTy Φ τ]
variable {D : Type d} [Category.{h} D] [CartesianMonoidalCategory D] [HasFiniteCoproducts D]

variable (M : TypeModel τ D)
variable (prim : ∀ f : Φ, M.obj (instrSrc f) ⟶ M.obj (instrTrg f))

/-- Interpret the ΛSSA primitive and expose its two typed alternatives. -/
noncomputable def stepMap {A : τ} (step : Step Φ A) :
    M.obj A ⟶ M.obj A ⨿ M.obj A :=
  eqToHom (congrArg M.obj step.input.symm) ≫ prim step.op ≫
    eqToHom (congrArg M.obj step.output) ≫ (M.coprodIso A A).hom

/-- Put the two alternatives on the RVSDG selector and value ports.
Each leg carries its own payload unchanged; the value port is right-padded
with the same unit as every singleton RVSDG boundary. -/
noncomputable def encodeStep (sel : Categorical.Selectors D) (X : D) :
    X ⨿ X ⟶ sel.obj 2 ⊗ (X ⊗ 𝟙_ D) :=
  coprod.desc ((ρ_ X).inv ≫ Categorical.selectorLeg (sel.tag (0 : Fin 2)))
    ((ρ_ X).inv ≫ Categorical.selectorLeg (sel.tag (1 : Fin 2)))

noncomputable def valueModel (sel : Categorical.Selectors D) :
    Categorical.Model (Opcode (τ := τ) Φ) D where
  selectors := sel
  value := M.obj
  snapshot s := s.elim
  primitive
    | .step step => (ρ_ _).hom ≫ stepMap M prim step ≫ encodeStep sel _

/-- The order of the padding unit differs between the two singleton
context conventions. -/
def entryMap (A : τ) : ctxObj M [A] ⟶ M.obj A ⊗ 𝟙_ D :=
  (λ_ (M.obj A)).hom ≫ (ρ_ (M.obj A)).inv

end Silmaril.SSA.RVSDG.LambdaSSA.Theta
