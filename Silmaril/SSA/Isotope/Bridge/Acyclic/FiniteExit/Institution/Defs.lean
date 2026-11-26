module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.FiniteExit.Categorical.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.FiniteExit.Signature.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Expansion.Institution.Thms

/-! # Exact equations and native satisfaction at finite exit interfaces -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution (Room)
open Morphism (SignatureMap)
open LambdaSSA.Acyclic (FiniteExit)
open LambdaSSA.Region (packedExitType)
open LambdaSSA.Semantics.Categorical (ctxObj labelObj denoteRegion)

variable {τ υ ε δ : Type} [TypeFormers τ] [TypeFormers υ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ}

/-- An equation keeps its bound context and its ordered external labels. -/
structure FiniteExitIndex (τ : Type) where
  depth : Nat
  bound : BoundCtx τ depth
  exits : List τ

abbrev FiniteExitEquation (P : InstrSig τ ε) :=
  Σ i : FiniteExitIndex τ,
    FiniteExit P.Instr i.exits i.bound × FiniteExit P.Instr i.exits i.bound

/-- Pack both native sides of the equation into ordinary exact SSA. -/
def encodeFiniteExit (e : FiniteExitEquation P) : SSAEquation P :=
  ⟨⟨e.1.depth, e.1.bound, packedExitType e.1.exits⟩, e.2.1.encode, e.2.2.encode⟩

/-- Compile a finite-exit equation into an exact LetCase equation. -/
def compileFiniteExit (e : FiniteExitEquation P) : CaseEquation P :=
  compile (encodeFiniteExit e)

/-- Map the ordered exit context and both exact region sides. -/
def mapFiniteExit (g : SignatureMap P.Instr Q.Instr τ υ ε δ) [g.PreservesProducts] [g.PreservesSums]
    (e : FiniteExitEquation P) : FiniteExitEquation Q :=
  ⟨⟨e.1.depth, e.1.bound.mapTypes g.ty, e.1.exits.map g.ty⟩,
    e.2.1.mapSignature g, e.2.2.mapSignature g⟩

variable {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]

/-- Use the existing positional region semantics at the unchanged label list. -/
noncomputable def CoherentRegionModel.denoteFiniteExit (K : CoherentRegionModel J P)
    {n : Nat} {β : BoundCtx τ n} {L : List τ} (c : FiniteExit P.Instr L β) :
    J.obj (ctxObj K.types β.toList) ⟶ J.obj (labelObj K.types L) :=
  letI := K.instructions
  denoteRegion J K.types c.toSSA_hasType

variable [FreydCategory.CentralUnit J]

/-- The coherent models act on natively denoted finite-exit equations. -/
noncomputable def finiteExitRoom (P : InstrSig τ ε) : Room.{0, 0, 1} where
  Sen := FiniteExitEquation P
  Mod := (ssaRoom J P).Mod
  Sat K e := (K.fromShrinkHoms.as.denoteFiniteExit J e.2.1) =
    (K.fromShrinkHoms.as.denoteFiniteExit J e.2.2)

end Silmaril.Isotope.Institution.Acyclic
