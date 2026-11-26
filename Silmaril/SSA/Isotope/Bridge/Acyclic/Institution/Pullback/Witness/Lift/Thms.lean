module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Pullback.Witness.Lift.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.WitnessLift

/-! # Exactly when a target region witness lifts on the relabelled interfaces -/

public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open Morphism (SignatureMap)

variable {τ υ ε δ : Type} [TypeFormers τ] [TypeFormers υ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ}
  (g : SignatureMap P.Instr Q.Instr τ υ ε δ)

/-- A constructor-preserving reverse signature map that is a left inverse
on types and primitives reflects region typing, including hidden binder
types and local label families. Effects need no left inverse. -/
theorem regionTypingReflects_of_split
    (back : SignatureMap Q.Instr P.Instr υ τ δ ε) [back.PreservesProducts] [back.PreservesSums]
    (types : Function.LeftInverse back.ty g.ty) (instructions : Function.LeftInverse back.instr g.instr) :
    RegionTypingReflects g :=
  regionTypingReflects_of_split_proof g back types instructions

variable [g.PreservesProducts] [g.PreservesSums]
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]

/-- For any coherent target model, lifting all witnessed denotation arrows at
the mapped interfaces is equivalent to reflection of positional typing.
Forward witness transport and target coherence provide the arrow equality
once the source judgement is typable. -/
theorem regionWitnessLifts_iff (K : CoherentRegionModel J Q) :
    RegionWitnessLifts g K ↔ RegionTypingReflects g :=
  regionWitnessLifts_iff_proof g K

end Silmaril.Isotope.Institution.Acyclic
