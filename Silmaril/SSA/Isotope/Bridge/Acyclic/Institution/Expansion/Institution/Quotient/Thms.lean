module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Expansion.Institution.Quotient.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.SemanticQuotient

/-! # The isomorphism on semantic classes of equations

The quotient identifies equations with the same satisfaction in the chosen
rooms. Completeness of a syntactic rewrite theory would additionally require
deriving equivalence from that agreement.
-/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution (Inst Room CoIns)
open Silmaril.SSA.LambdaRTL.Quotient (semSetoid quotFunctor)

/-- In either room diagram, equivalent equations remain equivalent under a
signature map by testing them in the reduct of each target model. -/
theorem semanticEquiv_map_signature (I : TypeSignature ⥤ Room.{0, 0, 1})
    {P Q : TypeSignature} (f : P ⟶ Q) {e d : (I.obj P).Sen}
    (h : (semSetoid (I.obj P)).r e d) :
    (semSetoid (I.obj Q)).r ((I.map f).sen e) ((I.map f).sen d) :=
  fun M => ((I.map f).sat M e).trans ((h ((I.map f).mod.obj M)).trans ((I.map f).sat M d).symm)

variable {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]

/-- The LetCase inverse law on classes is inherited from the exact sentence
round trip. -/
theorem compile_reify_class (P : TypeSignature) (q : ((validatedSemanticInstitution J).I.obj P).Sen) :
    ((semanticCompile J).ρ.app P).sen (((semanticReify J).ρ.app P).sen q) = q :=
  compile_reify_class_proof J P q

/-- The SSA inverse law on classes uses satisfaction in every coherent
model. -/
theorem reify_compile_class (P : TypeSignature) (q : ((ssaSemanticInstitution J).I.obj P).Sen) :
    ((semanticReify J).ρ.app P).sen (((semanticCompile J).ρ.app P).sen q) = q :=
  reify_compile_class_proof J P q

/-- Reification followed by compilation is the identity corridor on the
validated quotient. -/
theorem semanticReify_compile (P : TypeSignature) :
    (semanticReify J).ρ.app P ≫ (semanticCompile J).ρ.app P =
      𝟙 ((validatedSemanticInstitution J).I.obj P) :=
  semanticReify_compile_proof J P

/-- Compilation followed by reification is the identity corridor on the
coherent SSA quotient. -/
theorem semanticCompile_reify (P : TypeSignature) :
    (semanticCompile J).ρ.app P ≫ (semanticReify J).ρ.app P =
      𝟙 ((ssaSemanticInstitution J).I.obj P) :=
  semanticCompile_reify_proof J P

/-- The quotiented diagrams are naturally isomorphic over the same
type-changing signatures, with the original discrete model isomorphism. -/
noncomputable def semanticComparisonNaturalIso :
    (validatedSemanticInstitution J).I ≅ (ssaSemanticInstitution J).I where
  hom := Functor.whiskerRight (validatedReifyNatural J) quotFunctor
  inv := Functor.whiskerRight (validatedCompileNatural J) quotFunctor
  hom_inv_id := NatTrans.ext (funext (semanticReify_compile J))
  inv_hom_id := NatTrans.ext (funext (semanticCompile_reify J))

/-- The descended comorphisms are inverse in the category of institutions
and comorphisms. -/
noncomputable def semanticInstitutionIso :
    Iso (C := CoIns.{1, 0, 0, 0, 1}) (validatedSemanticInstitution J) (ssaSemanticInstitution J) where
  hom := semanticReify J
  inv := semanticCompile J
  hom_inv_id := Inst.CoHom.ext rfl (NatTrans.ext (funext (semanticReify_compile J)))
  inv_hom_id := Inst.CoHom.ext rfl (NatTrans.ext (funext (semanticCompile_reify J)))

end Silmaril.Isotope.Institution.Acyclic
