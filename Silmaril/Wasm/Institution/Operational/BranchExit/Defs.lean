module

public import Silmaril.Logic.Operational.SOS.Thms
public import Silmaril.Wasm.Execution.Runtime

/-! # Branching across two block labels

A branch at depth one leaves its inner label, retaining the operand stack.
At the outer label the depth-zero branch retains only the typed result
suffix. Both block continuations are empty.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.BranchExit

open Silmaril.Logic.Operational Silmaril.Logic.Operational.SOS Silmaril.Semantics.SOS
open Silmaril.Wasm.Execution.Runtime (Value)

inductive State where
  | nested (innerArity : Nat) (discard result : List Value)
  | outer (discard result : List Value)
  | done (result : List Value)

def State.results : State → List Value
  | .nested _ _ result | .outer _ result | .done result => result

def Admitted (resultType : Option NumType) (a : State) : Prop :=
  a.results.map Value.type = resultType.toList

inductive Outcome (resultType : Option NumType) : State → State → Prop where
  | cross (innerArity : Nat) (discard result : List Value) :
      Outcome resultType (.nested innerArity discard result) (.outer discard result)
  | finish (discard result : List Value) (typed : result.map Value.type = resultType.toList) :
      Outcome resultType (.outer discard result) (.done result)

abbrev Judgment := State × State
def shape : SOS.Shape.{0} := ⟨⟨State, Unit⟩, Judgment, fun (a, _, b) => (a, b)⟩
def presentation (resultType : Option NumType) : SOS.Presentation :=
  ⟨shape, {r | r.premises = [] ∧ Outcome resultType r.conclusion.1 r.conclusion.2}⟩

abbrev Edge (resultType : Option NumType) (a b : State) := (presentation resultType).Derives (a, b)
abbrev Runs (resultType : Option NumType) := Relation.ReflTransGen (Edge resultType)

end Silmaril.Wasm.Institution.Operational.BranchExit
