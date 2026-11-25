module

public import Silmaril.Languages.Starlark.Functions.Lowering.Defs
public import Silmaril.Languages.Starlark.Functions.Operational.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Functions.Lowering

open Lists (State Outcome)
open Lists.Iteration (Flow truth)

def Scratch (start : Nat) (binding : Binding) : Prop :=
  ∃ index, start ≤ index ∧ binding = temporary index

/-- Scratch writes use the frame's direct bindings and allocate no heap cells. -/
def ScratchFree (state : State) : Prop :=
  ∀ index, state.slots (temporary index) = none

/-- Keep the entire heap, iterator stack and lexical slot map. Ignore only the
direct bindings of compiler scratch names at or above the given offset. -/
structure StateMatch (start : Nat) (source target : State) : Prop where
  heap : source.heap = target.heap
  iterators : source.iterators = target.iterators
  slots : source.slots = target.slots
  bindings : ∀ name, ¬ Scratch start name → source.bindings name = target.bindings name

/-- The call-free atoms may refer to any non-scratch binding. -/
inductive AtomSafe : {α : Type} → Lists.Code α → Prop where
  | scalar (value : Starlark.Value) : AtomSafe (.scalar value)
  | builtin (id : Lists.Builtin) : AtomSafe (.builtin id)
  | string (text : String) : AtomSafe (.string text)
  | predeclared (value : Starlark.Value) : AtomSafe (.read (.predeclared value))
  | bound {name : Binding} : ¬ Scratch 0 name → AtomSafe (.read (.bound name))
  | list {values : Lists.Code (List Lists.Value)} : AtomSafe values → AtomSafe (.list values)
  | tuple {values : Lists.Code (List Lists.Value)} : AtomSafe values → AtomSafe (.tuple values)
  | dict {entries : Lists.Code (List Lists.Entry)} : AtomSafe entries → AtomSafe (.dict entries)
  | noEntries : AtomSafe .noEntries
  | entry {entries : Lists.Code (List Lists.Entry)} {key value : Lists.Expr} :
      AtomSafe entries → AtomSafe key → AtomSafe value → AtomSafe (.entry entries key value)
  | empty : AtomSafe .empty
  | cons {head : Lists.Expr} {tail : Lists.Code (List Lists.Value)} :
      AtomSafe head → AtomSafe tail → AtomSafe (.cons head tail)
  | index {receiver index : Lists.Expr} :
      AtomSafe receiver → AtomSafe index → AtomSafe (.index receiver index)
  | append {receiver value : Lists.Expr} :
      AtomSafe receiver → AtomSafe value → AtomSafe (.append receiver value)

def positionalShape (arity : Nat) : Arguments :=
  { positional := List.replicate arity (.scalar .none) }

def callValue : Flow → Lists.Value
  | .returned value => value
  | _ => .scalar .none

/-- Application operates on values already evaluated by the source rules.
It uses the shared dispatch and independent core semantics for callee bodies. -/
inductive Applies (program : Program) (available : List DeclarationId) (arity : Nat)
    (state : State) (values : List Lists.Value) : Outcome Lists.Value → Prop where
  | reject {error : Lists.Error} {next : State} :
      prepare program available (positionalShape arity) values state = .error error next →
      Applies program available arity state values (.error error next)
  | builtin {id : Lists.Builtin} {actual : Actual} {next : State} {out : Outcome Lists.Value} :
      prepare program available (positionalShape arity) values state = .ok (.builtin id actual) next →
      Builtins.Invokes next id actual out →
      Applies program available arity state values out
  | returned {plan : Prepared available} {next final : State} {flow : Flow} :
      prepare program available (positionalShape arity) values state = .ok (.closure plan) next →
      Exec program (withoutDeclaration available plan.id) next plan.body (.ok flow final) →
      Applies program available arity state values (.ok (callValue flow) (restoreCaller state final))
  | failed {plan : Prepared available} {next final : State} {error : Lists.Error} :
      prepare program available (positionalShape arity) values state = .ok (.closure plan) next →
      Exec program (withoutDeclaration available plan.id) next plan.body (.error error final) →
      Applies program available arity state values (.error error (restoreCaller state final))

mutual
/-- Source rules for the positional-call fragment. Short-circuiting returns
the selected operand value. No rule mentions emitted code or scratch names. -/
inductive Evaluates (program : Program) (available : List DeclarationId) :
    State → Expr → Outcome Lists.Value → Prop where
  | atom {s : State} {expression : Lists.Expr} {out : Outcome Lists.Value} :
      AtomSafe expression → Lists.Eval s expression out →
      Evaluates program available s (.atom expression) out
  | call {s t : State} {callee : Expr} {args : List Expr} {values : List Lists.Value}
      {out : Outcome Lists.Value} :
      EvaluatesMany program available s (callee :: args) (.ok values t) →
      Applies program available args.length t values out →
      Evaluates program available s (.callPos callee args) out
  | callError {s t : State} {callee : Expr} {args : List Expr} {error : Lists.Error} :
      EvaluatesMany program available s (callee :: args) (.error error t) →
      Evaluates program available s (.callPos callee args) (.error error t)
  | branch {s t : State} {test yes no : Expr} {tested out : Outcome Lists.Value} {flag : Bool} :
      Evaluates program available s test tested →
      Outcome.resume tested truth = .ok flag t →
      Evaluates program available t (if flag then yes else no) out →
      Evaluates program available s (.branch test yes no) out
  | branchError {s t : State} {test yes no : Expr} {tested : Outcome Lists.Value} {error : Lists.Error} :
      Evaluates program available s test tested →
      Outcome.resume tested truth = .error error t →
      Evaluates program available s (.branch test yes no) (.error error t)
  | logical {s t : State} {op : LogicalOp} {left right : Expr} {value : Lists.Value}
      {flag : Bool} {out : Outcome Lists.Value} :
      Evaluates program available s left (.ok value t) →
      truth value t = .ok flag t →
      (if op = .and then flag else !flag) = true →
      Evaluates program available t right out →
      Evaluates program available s (.logical op left right) out
  | shortCircuit {s t : State} {op : LogicalOp} {left right : Expr} {value : Lists.Value} {flag : Bool} :
      Evaluates program available s left (.ok value t) →
      truth value t = .ok flag t →
      (if op = .and then flag else !flag) = false →
      Evaluates program available s (.logical op left right) (.ok value t)
  | logicalError {s t : State} {op : LogicalOp} {left right : Expr}
      {tested : Outcome Lists.Value} {error : Lists.Error} :
      Evaluates program available s left tested →
      Outcome.resume tested truth = .error error t →
      Evaluates program available s (.logical op left right) (.error error t)

inductive EvaluatesMany (program : Program) (available : List DeclarationId) :
    State → List Expr → Outcome (List Lists.Value) → Prop where
  | empty {s : State} : EvaluatesMany program available s [] (.ok [] s)
  | cons {s t u : State} {head : Expr} {tail : List Expr} {value : Lists.Value}
      {values : List Lists.Value} :
      Evaluates program available s head (.ok value t) →
      EvaluatesMany program available t tail (.ok values u) →
      EvaluatesMany program available s (head :: tail) (.ok (value :: values) u)
  | headError {s t : State} {head : Expr} {tail : List Expr} {error : Lists.Error} :
      Evaluates program available s head (.error error t) →
      EvaluatesMany program available s (head :: tail) (.error error t)
  | tailError {s t u : State} {head : Expr} {tail : List Expr} {value : Lists.Value}
      {error : Lists.Error} :
      Evaluates program available s head (.ok value t) →
      EvaluatesMany program available t tail (.error error u) →
      EvaluatesMany program available s (head :: tail) (.error error u)
end

end Silmaril.Languages.Starlark.Functions.Lowering
