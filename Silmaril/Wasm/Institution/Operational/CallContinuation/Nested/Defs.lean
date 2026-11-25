module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.Defs

/-! # One resolved nested call

The outer function has already entered its frame and block label. The inner
resolved invocation runs with one saved `nop` in the outer body. This slice
includes both outer exits after the inner call resumes or traps.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.Nested

open Silmaril.Logic.Operational Silmaril.Logic.Operational.SOS Silmaril.Semantics.SOS
open Execution.Runtime (Value)

inductive Result where
  | values (stack : List Value)
  | trap

inductive State where
  | label (body : CallContinuation.State)
  | exit (result : Result)
  | done (result : Result)

def Admitted (fn : CallFrame.Callee) : State → Prop
  | .label body => CallContinuation.Admitted fn body
  | _ => True

inductive Ground (arity : Nat) : State → State → Prop where
  | labelValues (stack : List Value) : Ground arity (.label (.done stack)) (.exit (.values stack))
  | labelTrap : Ground arity (.label (.trapped [] false)) (.exit .trap)
  | frameValues (stack : List Value) (length : stack.length = arity) :
      Ground arity (.exit (.values stack)) (.done (.values stack))
  | frameTrap : Ground arity (.exit .trap) (.done .trap)

inductive Judgment where
  | body (edge : CallContinuation.Judgment)
  | step (source target : State)

inductive RuleInstance (fn : CallFrame.Callee) (arity : Nat) : Rule Judgment → Prop where
  | body {r : Rule CallContinuation.Judgment} (rule : CallContinuation.RuleInstance fn r) :
      RuleInstance fn arity ⟨r.premises.map .body, .body r.conclusion⟩
  | context (a b : CallContinuation.State) :
      RuleInstance fn arity ⟨[.body (.outer a b)], .step (.label a) (.label b)⟩
  | ground {a b : State} (rule : Ground arity a b) : RuleInstance fn arity ⟨[], .step a b⟩

def shape : SOS.Shape.{0} := ⟨⟨State, Unit⟩, Judgment, fun (a, _, b) => .step a b⟩
def presentation (fn : CallFrame.Callee) (arity : Nat) : SOS.Presentation :=
  ⟨shape, {r | RuleInstance fn arity r}⟩

abbrev Edge (fn : CallFrame.Callee) (arity : Nat) (a b : State) := (presentation fn arity).Derives (.step a b)
abbrev Runs (fn : CallFrame.Callee) (arity : Nat) := Relation.ReflTransGen (Edge fn arity)

end Silmaril.Wasm.Institution.Operational.CallContinuation.Nested
