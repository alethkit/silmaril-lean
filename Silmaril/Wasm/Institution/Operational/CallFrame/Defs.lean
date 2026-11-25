module

public import Silmaril.Wasm.Institution.Operational.Locals.Thms

/-! # A typed numeric call frame

A resolved call enters one allocated Wasm function with a numeric signature
and at most one result. A callee body is flat local code, numeric constants
followed by an explicit return, or one unreachable instruction. These bodies
exclude nested calls and additional control contexts. The caller supplies
a value prefix and no instruction continuation. Values are in evaluation order,
with the top of the stack at the right end of the list.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallFrame

open Silmaril.Logic.Operational Silmaril.Logic.Operational.SOS Silmaril.Semantics.SOS
open Silmaril.Wasm.Execution.Runtime (ModuleInst Value)

inductive Program where
  | locals (code : List Locals.Op)
  | ret (stack : List Value)
  | unreachable

structure Callee where
  module : ModuleInst
  typeIndex : TypeIdx
  params : List NumType
  locals : List NumType
  result : Option NumType
  program : Program

def Callee.localTypes (fn : Callee) : List NumType := fn.params ++ fn.locals

def Callee.arity (fn : Callee) : Nat := fn.result.toList.length

def Callee.init (fn : Callee) (args : List Value) : List Value :=
  args ++ fn.locals.map Value.zero

inductive Body where
  | code (program : Program)
  | trap

inductive Exit where
  | values (stack : List Value)
  | ret (stack : List Value)
  | trap

inductive State where
  | invoke (saved args : List Value)
  | label (saved locals : List Value) (body : Body)
  | exit (saved locals : List Value) (ready : Exit)
  | returned (saved results : List Value)
  | trapped (saved : List Value)

inductive Judgment where
  | body (edge : Locals.Judgment)
  | call (source target : State)

inductive Ground (fn : Callee) : State → State → Prop where
  | enter (saved args : List Value) (arity : args.length = fn.params.length) :
      Ground fn (.invoke saved args) (.label saved (fn.init args) (.code fn.program))
  | unreachable (saved ls : List Value) :
      Ground fn (.label saved ls (.code .unreachable)) (.label saved ls .trap)
  | labelValues (saved ls stack : List Value) :
      Ground fn (.label saved ls (.code (.locals (Locals.values stack))))
        (.exit saved ls (.values stack))
  | labelReturn (saved ls stack : List Value) :
      Ground fn (.label saved ls (.code (.ret stack))) (.exit saved ls (.ret stack))
  | labelTrap (saved ls : List Value) :
      Ground fn (.label saved ls .trap) (.exit saved ls .trap)
  | frameValues (saved ls stack : List Value) (arity : stack.length = fn.arity) :
      Ground fn (.exit saved ls (.values stack)) (.returned saved stack)
  | frameReturn (saved ls extra results : List Value) (arity : results.length = fn.arity) :
      Ground fn (.exit saved ls (.ret (extra ++ results))) (.returned saved results)
  | frameTrap (saved ls : List Value) :
      Ground fn (.exit saved ls .trap) (.trapped saved)
  | bubble (saved discarded : List Value) (nonempty : discarded ≠ []) :
      Ground fn (.trapped (saved ++ discarded)) (.trapped saved)

inductive RuleInstance (fn : Callee) : Rule Judgment → Prop where
  | body {r : Rule Locals.Judgment} (rule : Locals.RuleInstance r) :
      RuleInstance fn ⟨r.premises.map .body, .body r.conclusion⟩
  | fact {a b : State} (h : Ground fn a b) : RuleInstance fn ⟨[], .call a b⟩
  | reduce (saved : List Value) (a b : Locals.State) :
      RuleInstance fn ⟨[.body (a, b)], .call (.label saved a.locals (.code (.locals a.code)))
        (.label saved b.locals (.code (.locals b.code)))⟩

def shape : SOS.Shape.{0} := ⟨⟨State, Unit⟩, Judgment, fun (a, _, b) => .call a b⟩

def presentation (fn : Callee) : SOS.Presentation := ⟨shape, {r | RuleInstance fn r}⟩

abbrev Edge (fn : Callee) (a b : State) := (presentation fn).Derives (.call a b)
abbrev Runs (fn : Callee) := Relation.ReflTransGen (Edge fn)

def RetTyped (fn : Callee) (stack : List Value) : Prop :=
  (stack.map Value.type).reverse.take fn.arity = fn.result.toList

def Program.Typed (fn : Callee) : Program → Prop
  | .locals code => Locals.check fn.localTypes [] code = some fn.result.toList
  | .ret stack => RetTyped fn stack
  | .unreachable => True

def Admitted (fn : Callee) : State → Prop
  | .invoke _ args => args.map Value.type = fn.params ∧ fn.program.Typed fn
  | .label _ ls (.code p) => ls.map Value.type = fn.localTypes ∧ p.Typed fn
  | .label _ ls .trap | .exit _ ls .trap => ls.map Value.type = fn.localTypes
  | .exit _ ls (.values stack) =>
      ls.map Value.type = fn.localTypes ∧ (stack.map Value.type).reverse = fn.result.toList
  | .exit _ ls (.ret stack) => ls.map Value.type = fn.localTypes ∧ RetTyped fn stack
  | .returned _ results => (results.map Value.type).reverse = fn.result.toList
  | .trapped _ => True

end Silmaril.Wasm.Institution.Operational.CallFrame
