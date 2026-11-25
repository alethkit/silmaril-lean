module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.InstructionFree.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Coproducts.Thms

/-! # A concrete projection square for one-block LambdaSSA feedback -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.ProjectionExample

open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory

abbrev Types := Ty Unit

scoped instance emptyInstructions : HasTy Empty Types where
  src := Empty.elim
  trg := Empty.elim

def flag : Types := .coprod .unit .unit
def payload : Types := .base ()
def state : Types := .product flag payload
def result : Types := state

/-- Unpack the state and return its right component. -/
def projectRight : Tm Empty := .let₂ (.var 0) (.var 0)

theorem projectRight_typed (Γ : VCtx Types) : Tm.HasType (state :: Γ) projectRight payload :=
  .let₂ (.var (i := 0) rfl) (.var (i := 0) rfl)

def repeatBody : Region Empty := .br 0 (.var 0)

theorem repeat_typed (A : Types) (Γ L : List Types) : ValueBranches (A :: Γ) repeatBody (A :: L) :=
  .br (ℓ := 0) rfl (.var (i := 0) rfl)

def loopBefore : Region Empty := .cfg repeatBody 1 (fun _ => repeatBody)

def loopAfter : Region Empty :=
  .cfg (repeatBody.lsubst (boundLocalMap projectRight)) 1 (fun _ => repeatBody)

theorem loopBefore_valueBranches : ValueBranches [state] loopBefore [result] :=
  .cfg (fun _ : Fin 1 => state) (repeat_typed state [] [result])
    (fun _ => repeat_typed state [state] [result])

theorem loopAfter_valueBranches : ValueBranches [state] loopAfter [result] :=
  .cfg (fun _ : Fin 1 => payload)
    (.let₁ (projectRight_typed []) (repeat_typed payload [state] [result]))
    (fun _ => repeat_typed payload [state] [result])

/-- The left path of the bound square, applying the projection to each repeat. -/
def repeatThenProject : Region Empty :=
  repeatBody.lsubst (liftLSubstVars (boundLocalMap projectRight))

/-- The right path of the bound square, entering the new block with the projected state. -/
def projectThenRepeat : Region Empty :=
  (Region.br 0 projectRight).bindBranchArguments.lsubst (liftLSubstVars (fun _ => repeatBody))

noncomputable def repeatBefore : ofType (Φ := Empty) state ⟶ ofType result ⨿ ofType state :=
  coprod.inr

noncomputable def repeatAfter : ofType (Φ := Empty) payload ⟶ ofType result ⨿ ofType payload :=
  coprod.inr

def stateChange : ofType (Φ := Empty) state ⟶ ofType payload :=
  returnTerm (projectRight_typed [])

end Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.ProjectionExample
