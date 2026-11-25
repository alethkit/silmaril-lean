module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.OrdinarySquare.Defs

/-! # A capture-free state change between two self-loops
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction

open CategoryTheory CategoryTheory.Limits
open Silmaril Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Paper.TypeCategory

scoped instance : HasTy Empty (Ty Empty) := ⟨Empty.elim, Empty.elim⟩

/-- The source state has two inhabitants and the target state is unit. -/
def state : Ty Empty := .coprod .unit .unit

def result : Ty Empty := .unit

/-- An instruction-free state change with a term-level unary let. -/
def changeState : Tm Empty := .let₁ (.var 0) .unit

theorem state_typed : Tm.HasType [state] changeState result :=
  .let₁ (.var (i := 0) rfl) .unit

def repeatBody : Region Empty := .br 0 (.var 0)

def entry : Region Empty := .br 0 (.inl .unit)

def before : Region Empty := CfgEta.singleCfg entry repeatBody

def after : Region Empty :=
  CfgEta.singleCfg (entry.lsubst (boundLocalMap changeState)) repeatBody

def localSource : Region Empty :=
  repeatBody.lsubst (liftLSubstVars (boundLocalMap changeState))

def localTarget : Region Empty :=
  (Region.br 0 changeState).bindBranchArguments.lsubst (liftLSubstVars (fun _ => repeatBody))

noncomputable def stateMap : ofType (Φ := Empty) state ⟶ ofType result :=
  boundReturn state_typed

noncomputable def sourceStep : ofType (Φ := Empty) state ⟶ ofType result ⨿ ofType state :=
  coprod.inr

noncomputable def targetStep : ofType (Φ := Empty) result ⟶ ofType result ⨿ ofType result :=
  coprod.inr

end Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction
