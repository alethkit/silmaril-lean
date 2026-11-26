module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Expansion.Institution.Thms
public import Silmaril.SSA.LambdaRTL.Quotient.Defs

/-! # Semantic sentence classes for the exact acyclic comparison -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution (Inst)
open Silmaril.SSA.LambdaRTL.Quotient

variable {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]

/-- Exact LetCase equations modulo satisfaction in every validated model. -/
noncomputable abbrev validatedSemanticInstitution : Inst.{1, 0, 0, 0, 1} :=
  Inst.quot (validatedCaseInstitution J)

/-- Exact SSA equations modulo satisfaction in every coherent model. -/
noncomputable abbrev ssaSemanticInstitution : Inst.{1, 0, 0, 0, 1} :=
  Inst.quot (ssaTypeInstitution J)

/-- Reification descends by the existing corridor satisfaction law. -/
noncomputable def semanticReify :
    Inst.CoHom (validatedSemanticInstitution J) (ssaSemanticInstitution J) :=
  CoHom.quot (validatedReifyComorphism J)

/-- Compilation descends by the existing corridor satisfaction law. -/
noncomputable def semanticCompile :
    Inst.CoHom (ssaSemanticInstitution J) (validatedSemanticInstitution J) :=
  CoHom.quot (validatedCompileComorphism J)

end Silmaril.Isotope.Institution.Acyclic
