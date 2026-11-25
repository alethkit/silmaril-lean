module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.CollapseObstruction.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Feedback.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Thms

/-! # A pure-feedback simulation fixture -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta.CollapseObstruction.Uniformity

open CategoryTheory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open scoped Silmaril.Isotope.LambdaSSA.Region.CfgEta.CollapseObstruction

def selfBody : Region Empty := .br 0 (.var 0)
def pureChange : Region Empty := .br 0 (.inr .unit)

def mapLocal : Nat → Region Empty
  | 0 => pureChange
  | i + 1 => labelId (i + 1)

theorem selfBody_typed : ValueBranches [stateType] selfBody [stateType, resultType] := .br rfl (.var rfl)

theorem pureChange_value : Tm.BranchValue [stateType] (.inr .unit : Tm Empty) stateType := .inr .unit

theorem pureChange_typed : ValueBranches [stateType] pureChange [stateType] := .br rfl pureChange_value

theorem mapLocal_typed : LSubst.ValueFamily ([] : VCtx (Ty Empty)) [stateType, resultType] [stateType, resultType] mapLocal := by
  intro i A hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    exact .br rfl pureChange_value
  | succ i => exact .br hi (.var rfl)

def selfLoop := feedbackRegion [stateType] (fun _ => selfBody) 0

def changeThenLoop : Region Empty :=
  pureChange.lsubst (liftLSubstVars (fun _ => selfLoop))

def stateInterface : ContinuationContext Empty ([] : VCtx (Ty Empty)) :=
  ContinuationContext.single stateType

def returnInterface : ContinuationContext Empty ([] : VCtx (Ty Empty)) :=
  ContinuationContext.single resultType

def stateChangeArrow : fromNative.obj stateInterface ⟶ fromNative.obj stateInterface :=
  fromNative.map (ContinuationContext.singletonToHom pureChange_typed)

def selfBodyArrow :
    fromNative.obj stateInterface ⟶ fromNative.obj (stateInterface.append returnInterface) :=
  fromNative.map (ContinuationContext.singletonToHom selfBody_typed)

def changeLocalArrow :
    fromNative.obj (stateInterface.append returnInterface) ⟶
    fromNative.obj (stateInterface.append returnInterface) :=
  toHom ⟨mapLocal, mapLocal_typed⟩

/-- The change of state is a pure singleton arrow in the return presentation. -/
def pureStateChange : CfgEta.TypeCategory.ofType (Φ := Empty) (Γ := []) stateType ⟶
    CfgEta.TypeCategory.ofType (Φ := Empty) (Γ := []) stateType :=
  CfgEta.TypeCategory.ofRegion pureChange_typed

end Silmaril.Isotope.LambdaSSA.Region.CfgEta.CollapseObstruction.Uniformity
