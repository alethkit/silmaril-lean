module

public import Silmaril.Wasm.Institution.Operational.CallFrame.Native.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Blocks.Context

open Execution.Runtime (Value)

/-- The operand prefix and instruction suffix outside an entered block label.
Its arity belongs to the block. -/
structure Scope (A : Type) where
  arity : Nat
  saved : List Value
  rest : List A

def Scope.plug {A : Type} (values : List Value → List A) (label : Nat → List A → A)
    (scope : Scope A) (body : List A) : List A :=
  values scope.saved ++ label scope.arity body :: scope.rest

/-- An explicit return propagating through already-entered block labels. -/
inductive Returning (A : Type) where
  | pending (stack : List Value) (rest : List A)
  | under (scope : Scope A) (body : Returning A)

def Returning.render {A : Type} (values : List Value → List A) (label : Nat → List A → A)
    (ret : A) : Returning A → List A
  | .pending stack rest => values stack ++ ret :: rest
  | .under scope body => scope.plug values label (body.render values label ret)

/-- The declared function results must be present in the innermost label's
operand stack. The block's fallthrough arity does not enter this check. -/
def Returning.Typed {A : Type} (results : List NumType) : Returning A → Prop
  | .pending stack _ => (stack.map Value.type).reverse.take results.length = results.reverse
  | .under _ body => body.Typed results

/-- Each step crosses one label. The label drops its inner tail and delivers
the entire operand list to the surrounding sequence. -/
inductive ReturnStep {A : Type} : Returning A → Returning A → Prop where
  | exit (scope : Scope A) (stack : List Value) (rest : List A) :
      ReturnStep (.under scope (.pending stack rest)) (.pending (scope.saved ++ stack) scope.rest)
  | under (scope : Scope A) {a b : Returning A} (step : ReturnStep a b) :
      ReturnStep (.under scope a) (.under scope b)

abbrev ReturnRuns {A : Type} := Relation.ReflTransGen (@ReturnStep A)

open Execution in
abbrev coreValues (stack : List Value) : List Core.Admin := Core.vals (stack.map Value.toCore)

open Execution in
def coreCode : Returning Core.Admin → List Core.Admin :=
  Returning.render coreValues (fun arity => .label arity []) (.plain .return_)

def limeCode : Returning Wasm.Lime1.Execution.Admin → List Wasm.Lime1.Execution.Admin :=
  Returning.render Wasm.Lime1.Execution.values (fun arity => .label arity []) (.source .return_)

def v1Code : Returning Wasm.V1.Execution.Admin → List Wasm.V1.Execution.Admin :=
  Returning.render Wasm.V1.Execution.values (fun arity => .label arity []) (.source .return_)

end Silmaril.Wasm.Institution.Operational.Blocks.Context
