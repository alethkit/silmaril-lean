module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Pullback.Witness.Thms

/-! # Reflection of typing and lifting of region denotation witnesses -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open Morphism (SignatureMap)
open LambdaSSA.Semantics.Categorical (ctxObj labelObj RegionDenotes)

variable {τ υ ε δ : Type} [TypeFormers τ] [TypeFormers υ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ}
  (g : SignatureMap P.Instr Q.Instr τ υ ε δ)

/-- Reflect region typing at fixed source syntax and interfaces from their
images under relabelling. The target typing may use any internal types. -/
def RegionTypingReflects : Prop :=
  ∀ {Γ : LambdaSSA.VCtx τ} {r : LambdaSSA.Region P.Instr} {L : LambdaSSA.LCtx τ},
    LambdaSSA.Region.HasType (Γ.map g.ty) (r.mapInstr g.instr) (L.map g.ty) →
    LambdaSSA.Region.HasType Γ r L

variable [g.PreservesProducts] [g.PreservesSums]
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]

/-- A target denotation witness for the image of a source region and its
interfaces has a source witness with the same arrow after transport.
This compares witnessed arrows, with no choice of an inverse on constructor
trees of witnesses. -/
def RegionWitnessLifts (K : CoherentRegionModel J Q) : Prop :=
  ∀ {Γ : LambdaSSA.VCtx τ} {r : LambdaSSA.Region P.Instr} {L : LambdaSSA.LCtx τ}
    {ht : LambdaSSA.Region.HasType (Γ.map g.ty) (r.mapInstr g.instr) (L.map g.ty)}
    {a : J.obj (ctxObj K.types (Γ.map g.ty)) ⟶ J.obj (labelObj K.types (L.map g.ty))},
    (letI := K.instructions; RegionDenotes J K.types ht a) →
    ∃ (hr : LambdaSSA.Region.HasType Γ r L)
      (f : J.obj (ctxObj (pullbackTypes g K.types) Γ) ⟶
        J.obj (labelObj (pullbackTypes g K.types) L)),
      (letI := pullbackInstructions g K.instructions
       RegionDenotes J (pullbackTypes g K.types) hr f) ∧ HEq f a

end Silmaril.Isotope.Institution.Acyclic
