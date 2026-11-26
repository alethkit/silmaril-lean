module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.ReturnFold.Defs

/-! Specialize a native loop's successor choice using a constant guard fact. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.GuardFold

open Diamond (Model Signature Ty ValueSort dataPorts)
open Diamond.SCCP (Fact)
open RVSDG (Tuple)
open ReturnFold (Literals Refusal appendLiteral)
open Semantics.Dataflow (Flat)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)}
variable {entrySigs headerSigs : List (List (Ty Data))} {out : ValueSort Data}

/-- Use a new literal as the predicate of the existing native tail test.
The entry column, feedback column, and result keep their original origins. -/
def withLiteral (g : Graph Op inputs carried entrySigs headerSigs out) (literal : Op [] .predicate) :
    Graph Op inputs carried entrySigs (headerSigs ++ [[.value .predicate]]) out :=
  let added := appendLiteral literal g.header
  { preheader := g.preheader
    header := added.flow
    phiInputs
      | .entry => g.phiInputs .entry
      | .backedge => (g.phiInputs .backedge).map (fun _ wire => added.keep wire)
    predicate := added.result
    result := added.keep g.result }

variable (m : Model.{u, v, w} Op) [BankDecidableEq m.value (dataPorts carried)]
variable (g : Graph Op inputs carried entrySigs headerSigs out) (input : Tuple (Fact m.value) (dataPorts inputs))

/-- Read the guard at the simultaneous solution, over the bank shared by
all finite arrivals. Bottom contributes neither tail successor. -/
def guardFact : Flat (ULift.{w} Bool) :=
  (headerFacts m g input (SCCP.solve m g input).2.1).guard

def rewrite (literals : Literals m .predicate) :
    Except Refusal (Graph Op inputs carried entrySigs (headerSigs ++ [[.value .predicate]]) out) :=
  match guardFact m g input with
  | .constant test => .ok (withLiteral g (literals.opcode test))
  | .bottom => .error .unseen
  | .overdefined => .error .overdefined

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.GuardFold
