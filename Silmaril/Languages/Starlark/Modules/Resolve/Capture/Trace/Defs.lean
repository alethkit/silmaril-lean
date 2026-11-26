module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Leaf.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace

open Functions

local notation "Expr" => Lowering.Resolve.SourceExpr

/-- An admitted identifier is available in the listed lexical scopes and
cannot name a compiler temporary. -/
@[expose] def Visible (names : List String) (name : String) : Prop :=
  name ∈ names ∧ name.toList.head? ≠ some '$'

/-- Read-only setup and call operands. Lookup and indexing can fail at runtime. -/
inductive Operand (globals : List String) : Expr → Prop where
  | read {name : String} : Visible globals name → Operand globals (.scalar (.read name))
  | int (value : Int) : Operand globals (.scalar (.int value))
  | string (value : String) : Operand globals (.string value)
  | index {receiver index : Expr} : Operand globals receiver → Operand globals index →
      Operand globals (.index receiver index)

/-- A setup assignment may also allocate a list or tuple of read-only operands. -/
inductive Initializer (globals : List String) : Expr → Prop where
  | operand {value : Expr} : Operand globals value → Initializer globals value
  | list {items : List Expr} : (∀ item ∈ items, Operand globals item) → Initializer globals (.list items)
  | tuple {items : List Expr} : (∀ item ∈ items, Operand globals item) → Initializer globals (.tuple items)

/-- The bounded definition grammar. Every wrapper only defines its child and
returns it. A leaf has a two-item mixed assignment and a return. -/
inductive Definitions (globals : List String) : List String → Forwarding.Chain → Prop where
  | mixed {enclosing parameters : List String} {name target rhs receiver index result : String} :
      (∀ param ∈ parameters, param.toList.head? ≠ some '$') →
      target.toList.head? ≠ some '$' →
      Visible (parameters ++ target :: enclosing ++ globals) rhs →
      Visible (parameters ++ target :: enclosing ++ globals) receiver →
      Visible (parameters ++ target :: enclosing ++ globals) index →
      Visible (parameters ++ target :: enclosing ++ globals) result →
      Definitions globals enclosing (.mixed name parameters
        ⟨target, .scalar (.read receiver), .scalar (.read index),
          .plain (.scalar (.read rhs)), .scalar (.read result)⟩)
  | wrapper {enclosing parameters : List String} {name : String} {child : Forwarding.Chain} :
      (∀ param ∈ parameters, param.toList.head? ≠ some '$') →
      child.name.toList.head? ≠ some '$' →
      Definitions globals (parameters ++ child.name :: enclosing) child →
      Definitions globals enclosing (.wrapper name parameters child)

@[expose] def invocation (callee destination : String) (arguments : List Expr) : Command :=
  .assign destination (.call (.scalar (.read callee)) arguments [] none none)

/-- After the final call, only setup assignments remain. -/
inductive Tail (globals : List String) : List Command → Prop where
  | nil : Tail globals []
  | assign {name : String} {value : Expr} {rest : List Command} :
      Visible globals name → Initializer globals value → Tail globals rest →
      Tail globals (.assign name value :: rest)

/-- Each successful wrapper call stores the next closure in a module name.
Setup assignments can occur between calls and cannot overwrite the live callee. -/
inductive Schedule (globals : List String) :
    String → Forwarding.Chain → List Command → Prop where
  | setup {chain : Forwarding.Chain} {name callee : String} {value : Expr} {rest : List Command} :
      Visible globals name → name ≠ callee → Initializer globals value → Schedule globals callee chain rest →
      Schedule globals callee chain (.assign name value :: rest)
  | wrapper {name callee : String} {parameters : List String} {child : Forwarding.Chain}
      {destination : String} {arguments : List Expr} {rest : List Command} :
      Visible globals destination → (∀ arg ∈ arguments, Operand globals arg) →
      Schedule globals destination child rest →
      Schedule globals callee (.wrapper name parameters child) (invocation callee destination arguments :: rest)
  | leaf {name callee : String} {parameters : List String} {body : MixedBody}
      {destination : String} {arguments : List Expr} {rest : List Command} :
      Visible globals destination → (∀ arg ∈ arguments, Operand globals arg) → Tail globals rest →
      Schedule globals callee (.mixed name parameters body) (invocation callee destination arguments :: rest)

/-- All target names in the supported module are global assignment or
definition names. Their order includes the potentially skipped suffix. -/
@[expose] def names : List Command → List String
  | .assign name _ :: rest | .define name _ _ :: rest => name :: names rest
  | _ :: rest => names rest
  | [] => []

@[expose] def root (chain : Forwarding.Chain) : Command :=
  .define chain.name (.required chain.parameters) chain.body

/-- The static input to trace construction. The normal module validator
still checks the emitted declaration table and rejects duplicate globals
and invalid signatures. -/
structure Profile (chain : Forwarding.Chain) (after : List Command) : Prop where
  rootName : chain.name.toList.head? ≠ some '$'
  definitions : Definitions (names (root chain :: after)) [] chain
  schedule : Schedule (names (root chain :: after)) chain.name chain after

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace
