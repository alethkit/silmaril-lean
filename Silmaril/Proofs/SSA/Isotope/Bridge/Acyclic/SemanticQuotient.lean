module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Expansion.Institution.Quotient.Defs

public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution (Room)
open Silmaril.SSA.LambdaRTL.Quotient (semSetoid)

variable {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]

theorem compile_reify_class_proof (P : TypeSignature)
    (q : ((validatedSemanticInstitution J).I.obj P).Sen) :
    ((semanticCompile J).ρ.app P).sen (((semanticReify J).ρ.app P).sen q) = q := by
  induction q using Quotient.ind with
  | _ e => exact congrArg (Quotient.mk (semSetoid (validatedRoom J P.prim))) (compile_reify e)

theorem reify_compile_class_proof (P : TypeSignature)
    (q : ((ssaSemanticInstitution J).I.obj P).Sen) :
    ((semanticReify J).ρ.app P).sen (((semanticCompile J).ρ.app P).sen q) = q := by
  induction q using Quotient.ind with
  | _ e => exact Quotient.sound (fun M => reify_compile_sat (J := J) (P := P.prim) M e)

theorem semanticReify_compile_proof (P : TypeSignature) :
    (semanticReify J).ρ.app P ≫ (semanticCompile J).ρ.app P =
      𝟙 ((validatedSemanticInstitution J).I.obj P) :=
  Room.hom_ext (funext (compile_reify_class_proof J P))
    (validatedModelIso (J := J) P.prim).unit_eq.symm

theorem semanticCompile_reify_proof (P : TypeSignature) :
    (semanticCompile J).ρ.app P ≫ (semanticReify J).ρ.app P =
      𝟙 ((ssaSemanticInstitution J).I.obj P) :=
  Room.hom_ext (funext (reify_compile_class_proof J P))
    (validatedModelIso (J := J) P.prim).counit_eq

end Silmaril.Isotope.Institution.Acyclic
