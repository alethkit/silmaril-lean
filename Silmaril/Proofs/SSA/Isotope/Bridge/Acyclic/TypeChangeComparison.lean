module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.TypeChange.LetCase.Thms

public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution (Room)
open Silmaril.Logic.Metatheory.TheoryModel
open Morphism (SignatureMap)

variable {τ υ ε δ : Type} [TypeFormers τ] [TypeFormers υ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ}
  (g : SignatureMap P.Instr Q.Instr τ υ ε δ) [g.PreservesProducts] [g.PreservesSums]
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]

theorem reifyType_natural_proof :
    PresSig.inst.map (typeCaseHom g) ≫ reifyCorridor J Q =
      reifyCorridor J P ≫ ssaSignatureCorridor g := by
  refine Room.hom_ext (funext fun e => ?_) (ssaModelFunctor_ext fun K => ?_)
  · change reify (PresSig.mapEquation (typeCaseHom g) e) = mapSSASignature g (reify e)
    exact (congrArg (reify (P := Q)) (typeCaseHom_translate g e)).trans (reify_mapCaseSignature g e)
  · exact (caseAlgebra_typeChange g K.fromShrinkHoms.as).symm

theorem ssaSignatureCorridor_primitive_proof {P Q : InstrSig τ ε} (f : P ⟶ Q) :
    ssaSignatureCorridor (J := J) f.toSignatureMap = ssaCorridor f :=
  Room.hom_ext (funext (mapSSASignature_primitive f)) (ssaSignatureCorridor_primitive_mod f)

end Silmaril.Isotope.Institution.Acyclic
