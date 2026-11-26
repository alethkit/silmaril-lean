module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.TypeChange.LetCase.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.TypeChangeComparison

/-! # The exact LetCase to structured SSA comorphism over type changes -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution (Inst)
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

/-- Reification and the algebra reduct give a natural square of the original
equation rooms along a type-changing map. -/
theorem reifyType_natural :
    PresSig.inst.map (typeCaseHom g) ≫ reifyCorridor J Q =
      reifyCorridor J P ≫ ssaSignatureCorridor g :=
  reifyType_natural_proof g

/-- The existing reification corridors form a natural transformation over
the type-changing signature category. -/
noncomputable def typeReifyNatural (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] : letCaseTypeInst ⟶ ssaTypeInst J where
  app P := reifyCorridor J P.prim
  naturality {_ _} f := reifyType_natural f.signatureMap

/-- Reification as an institution comorphism over type-changing signatures.
Its reduct acts from coherent SSA models to LetCase operation algebras. -/
noncomputable def typeReifyComorphism (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] : Inst.CoHom letCaseTypeInstitution (ssaTypeInstitution J) where
  Φ := 𝟭 TypeSignature
  ρ := typeReifyNatural J ≫ (Functor.leftUnitor (ssaTypeInst J)).inv

/-- Primitive inclusion recovers the full original SSA corridor, including
the exact typed sentence map. -/
theorem ssaSignatureCorridor_primitive {P Q : InstrSig τ ε} (f : P ⟶ Q) :
    ssaSignatureCorridor (J := J) f.toSignatureMap = ssaCorridor f :=
  ssaSignatureCorridor_primitive_proof f

/-- The existing fixed-type comorphism uses the same components after primitive
inclusion. Both signature actions restrict by `typeCaseHom_primitive`
and `ssaSignatureCorridor_primitive`. -/
theorem typeReifyComorphism_primitive_app (P : InstrSig τ ε) :
    (typeReifyComorphism J).ρ.app ((TypeSignature.includePrimitive τ ε).obj P) =
      (reifyComorphism J τ ε).ρ.app P := rfl

end Silmaril.Isotope.Institution.Acyclic
