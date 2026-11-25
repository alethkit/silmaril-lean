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

def callValue : Flow → Lists.Value
  | .returned value => value
  | _ => .scalar .none

/-- Expansion runs only after all operands have evaluated. The pinned
profile checks the mapping before the iterable. -/
inductive Expands (args : EvaluatedArguments) (state : State) : Outcome Actual → Prop where
  | mappingError {error : Lists.Error} {next : State} :
      expandStarStar args.starStar state = .error error next →
      Expands args state (.error error next)
  | spreadError {keys : List (String × Lists.Value)} {next final : State} {error : Lists.Error} :
      expandStarStar args.starStar state = .ok keys next →
      expandStar args.star next = .error error final →
      Expands args state (.error error final)
  | success {keys : List (String × Lists.Value)} {values : List Lists.Value} {next final : State} :
      expandStarStar args.starStar state = .ok keys next →
      expandStar args.star next = .ok values final →
      Expands args state (.ok ⟨args.positional ++ values, args.keywords ++ keys⟩ final)

/-- Dispatch shares value-level call preparation, including argument binding,
and uses independent core semantics to execute a callee body. -/
inductive Dispatches (program : Program) (available : List DeclarationId)
    (state : State) (callee : Lists.Value) (actual : Actual) : Outcome Lists.Value → Prop where
  | reject {error : Lists.Error} {next : State} :
      prepareExpanded program available actual callee state = .error error next →
      Dispatches program available state callee actual (.error error next)
  | builtin {id : Lists.Builtin} {bound : Actual} {next : State} {out : Outcome Lists.Value} :
      prepareExpanded program available actual callee state = .ok (.builtin id bound) next →
      Builtins.Invokes next id bound out →
      Dispatches program available state callee actual out
  | returned {plan : Prepared available} {next final : State} {flow : Flow} :
      prepareExpanded program available actual callee state = .ok (.closure plan) next →
      Exec program (withoutDeclaration available plan.id) next plan.body (.ok flow final) →
      Dispatches program available state callee actual (.ok (callValue flow) (restoreCaller state final))
  | failed {plan : Prepared available} {next final : State} {error : Lists.Error} :
      prepareExpanded program available actual callee state = .ok (.closure plan) next →
      Exec program (withoutDeclaration available plan.id) next plan.body (.error error final) →
      Dispatches program available state callee actual (.error error (restoreCaller state final))

inductive Applies (program : Program) (available : List DeclarationId) (shape : ArgumentShape)
    (state : State) : List Lists.Value → Outcome Lists.Value → Prop where
  | expansionError {callee : Lists.Value} {operands : List Lists.Value}
      {error : Lists.Error} {next : State} :
      Expands (shape.collect operands) state (.error error next) →
      Applies program available shape state (callee :: operands) (.error error next)
  | expanded {callee : Lists.Value} {operands : List Lists.Value}
      {actual : Actual} {next : State} {out : Outcome Lists.Value} :
      Expands (shape.collect operands) state (.ok actual next) →
      Dispatches program available next callee actual out →
      Applies program available shape state (callee :: operands) out

/-- In resolved calls, keyword expressions follow the positional expressions.
The optional iterable and mapping expressions follow in that order. -/
def sourceOperands (callee : Expr) (positional : List Expr) (keywords : List (String × Expr))
    (star starStar : Option Expr) : List Expr :=
  callee :: (positional ++ keywords.map Prod.snd ++ star.toList ++ starStar.toList)

mutual
/-- Source rules evaluate operands left to right and stop at the first
error. A short-circuit returns the selected operand value. -/
inductive Evaluates (program : Program) (available : List DeclarationId) :
    State → Expr → Outcome Lists.Value → Prop where
  | atom {s : State} {expression : Lists.Expr} {out : Outcome Lists.Value} :
      AtomSafe expression → Lists.Eval s expression out →
      Evaluates program available s (.atom expression) out
  | call {s t : State} {callee : Expr} {positional : List Expr} {keywords : List (String × Expr)}
      {star starStar : Option Expr} {values : List Lists.Value} {out : Outcome Lists.Value} :
      EvaluatesMany program available s (sourceOperands callee positional keywords star starStar)
        (.ok values t) →
      Applies program available (argumentShape positional keywords star starStar) t values out →
      Evaluates program available s (.call callee positional keywords star starStar) out
  | callError {s t : State} {callee : Expr} {positional : List Expr} {keywords : List (String × Expr)}
      {star starStar : Option Expr} {error : Lists.Error} :
      EvaluatesMany program available s (sourceOperands callee positional keywords star starStar)
        (.error error t) →
      Evaluates program available s (.call callee positional keywords star starStar) (.error error t)
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
