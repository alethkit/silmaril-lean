module

public import Silmaril.Wasm.Institution.Operational.CallFrame.Defs

/-! # A resolved call followed by a saved instruction

The continuation is one `nop`. Within the callee the resume instruction stays
in the caller. A return restores the values before the instruction executes.
A trap can discard the instruction and some or all of the saved operands.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation

open Silmaril.Logic.Operational Silmaril.Logic.Operational.SOS Silmaril.Semantics.SOS
open Execution.Runtime (Value)

inductive State where
  | active (callee : CallFrame.State)
  | resume (stack : List Value)
  | done (stack : List Value)
  | trapped (stack : List Value) (hasTail : Bool)

def Active : CallFrame.State → Prop
  | .invoke .. | .label .. | .exit .. => True
  | .returned .. | .trapped .. => False

def attach : CallFrame.State → State
  | .returned saved results => .resume (saved ++ results)
  | .trapped saved => .trapped saved true
  | q => .active q

def Admitted (fn : CallFrame.Callee) : State → Prop
  | .active q => Active q ∧ CallFrame.Admitted fn q
  | _ => True

inductive Judgment where
  | inner (edge : CallFrame.Judgment)
  | outer (source target : State)

inductive Ground : State → State → Prop where
  | resume (stack : List Value) : Ground (.resume stack) (.done stack)
  | discardValues (kept removed : List Value) (hasTail : Bool) (nonempty : removed ≠ []) :
      Ground (.trapped (kept ++ removed) hasTail) (.trapped kept hasTail)
  | discardTail (kept removed : List Value) :
      Ground (.trapped (kept ++ removed) true) (.trapped kept false)

inductive RuleInstance (fn : CallFrame.Callee) : Rule Judgment → Prop where
  | inner {r : Rule CallFrame.Judgment} (rule : CallFrame.RuleInstance fn r) :
      RuleInstance fn ⟨r.premises.map .inner, .inner r.conclusion⟩
  | call (a b : CallFrame.State) (live : Active a) :
      RuleInstance fn ⟨[.inner (.call a b)], .outer (.active a) (attach b)⟩
  | ground {a b : State} (rule : Ground a b) : RuleInstance fn ⟨[], .outer a b⟩

def shape : SOS.Shape.{0} := ⟨⟨State, Unit⟩, Judgment, fun (a, _, b) => .outer a b⟩
def presentation (fn : CallFrame.Callee) : SOS.Presentation := ⟨shape, {r | RuleInstance fn r}⟩
abbrev Edge (fn : CallFrame.Callee) (a b : State) := (presentation fn).Derives (.outer a b)
abbrev Runs (fn : CallFrame.Callee) := Relation.ReflTransGen (Edge fn)

end Silmaril.Wasm.Institution.Operational.CallContinuation
