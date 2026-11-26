module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Expansion.Laws.Defs
public import Silmaril.Logic.Institution.Faithful
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.ExpansionLaws

/-! # Let-η and an obstruction to arbitrary algebra expansion -/

public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution (Corridor)
open Isotope.LetCase.LocallyNameless
open LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {τ ε : Type} [TypeFormers τ] {P : InstrSig τ ε}
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  {J : V ⥤ C}

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)

/-- The checked central-unit law makes let-η valid in the categorical
LetCase algebra, independently of iteration. -/
theorem freydCaseAlgebra_sat_letReturn [DistributiveFreydCategory J] [FreydCategory.CentralUnit J]
    (M : TypeModel τ V) (I : InstructionModel J M P.Instr)
    {n : Nat} {β : BoundCtx τ n} {A : τ} {t : Tm Empty P.Instr n}
    (d : Derivation P.Instr Γ₀ β t A) :
    ((LetCase.inst Γ₀).obj P).Sat (freydCaseAlgebra J M I) (letReturnEquation d) :=
  freydCaseAlgebra_sat_letReturn_proof M I d

/-- Raw LetCase operation algebras can reject even the closed unit instance
of let-η. -/
theorem letReturnCountermodel_rejects (P : InstrSig τ ε) :
    ¬ ((LetCase.inst Γ₀).obj P).Sat (letReturnCountermodel P) (unitLetReturn P) :=
  letReturnCountermodel_rejects_proof P

/-- The countermodel already lacks a distributive Freyd presentation with
central unit. -/
theorem letReturnCountermodel_noFreyd [DistributiveFreydCategory J] [FreydCategory.CentralUnit J]
    (M : TypeModel τ V) (I : InstructionModel J M P.Instr) :
    freydCaseAlgebra J M I ≠ letReturnCountermodel P := by
  intro h
  exact letReturnCountermodel_rejects P (h ▸ freydCaseAlgebra_sat_letReturn M I .unit)

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]

/-- The common coherent SSA class validates an equation that the full LetCase
algebra class rejects, so the corridor fails unrestricted reflection. -/
theorem reifyCorridor_not_faithful (P : InstrSig τ ε) :
    ¬ (reifyCorridor J P).Faithful :=
  reifyCorridor_not_faithful_proof P

/-- In particular the corridor cannot expand every raw algebra even up to
agreement on exact equations. -/
theorem reifyCorridor_not_elemExpansive (P : InstrSig τ ε) :
    ¬ (reifyCorridor J P).ElemExpansive :=
  fun h => reifyCorridor_not_faithful P h.faithful

end Silmaril.Isotope.Institution.Acyclic
