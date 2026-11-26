module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.TwoExit.Categorical.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.TwoExit.Signature.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Expansion.TypeChange.Thms

/-! # Exact equations at a two-exit interface -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open Morphism (SignatureMap)
open LambdaSSA.Acyclic (TwoExit)
open LambdaSSA.Semantics.Categorical (ctxObj labelObj denoteRegion)

variable {τ υ ε δ : Type} [TypeFormers τ] [TypeFormers υ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ}

/-- The two exits keep their ordered payload types, even if those types
happen to coincide. -/
structure TwoExitIndex (τ : Type) where
  depth : Nat
  bound : BoundCtx τ depth
  left : τ
  right : τ

abbrev TwoExitEquation (P : InstrSig τ ε) :=
  Σ i : TwoExitIndex τ,
    TwoExit P.Instr i.left i.right i.bound × TwoExit P.Instr i.left i.right i.bound

/-- Tag the native exit interface to obtain an ordinary exact SSA equation. -/
def encodeTwoExit (e : TwoExitEquation P) : SSAEquation P :=
  ⟨⟨e.1.depth, e.1.bound, coprod e.1.left e.1.right⟩, e.2.1.encode, e.2.2.encode⟩

/-- The resulting exact LetCase equation has a binary coproduct result. -/
def compileTwoExit (e : TwoExitEquation P) : CaseEquation P :=
  compile (encodeTwoExit e)

/-- Relabel both sides at the mapped two-exit interface. -/
def mapTwoExit (g : SignatureMap P.Instr Q.Instr τ υ ε δ) [g.PreservesProducts] [g.PreservesSums]
    (e : TwoExitEquation P) : TwoExitEquation Q :=
  ⟨⟨e.1.depth, e.1.bound.mapTypes g.ty, g.ty e.1.left, g.ty e.1.right⟩,
    e.2.1.mapSignature g, e.2.2.mapSignature g⟩

variable {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]

/-- Use the actual positional region denotation with two external labels. -/
noncomputable def CoherentRegionModel.denoteTwoExit (K : CoherentRegionModel J P)
    {n : Nat} {β : BoundCtx τ n} {A B : τ} (c : TwoExit P.Instr A B β) :
    J.obj (ctxObj K.types β.toList) ⟶ J.obj (labelObj K.types [A, B]) :=
  letI := K.instructions
  denoteRegion J K.types c.toSSA_hasType

/-- Satisfaction compares the native two-exit computation arrows. -/
def CoherentRegionModel.satTwoExit (K : CoherentRegionModel J P) (e : TwoExitEquation P) : Prop :=
  K.denoteTwoExit e.2.1 = K.denoteTwoExit e.2.2

end Silmaril.Isotope.Institution.Acyclic
