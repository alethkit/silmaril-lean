module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.WithDefaults

open Functions
open Lists (State Outcome)
open Trace.Defaults (Definition)

local notation "Expr" => Lowering.Resolve.SourceExpr
local notation "Value" => Lists.Value

/-- The existing wrapper and mixed-leaf chains can coexist with a module
function that has positional defaults and returns one parameter. -/
inductive Callable where
  | required (chain : Forwarding.Chain)
  | defaulted (definition : Definition)

@[expose] def Callable.name : Callable → String
  | .required chain => chain.name
  | .defaulted definition => definition.name

@[expose] def Callable.command : Callable → Command
  | .required chain => root chain
  | .defaulted definition => definition.command

@[expose] def Callable.Admitted (globals : List String) : Callable → Prop
  | .required chain => Trace.Definitions globals [] chain
  | .defaulted definition => Trace.Defaults.Admitted globals definition

@[expose] def Callable.returned : Callable → Option Callable
  | .required (.wrapper _ _ child) => some (.required child)
  | .required (.mixed ..) | .defaulted _ => none

abbrev Entries := String → Option Callable

@[expose] def Entries.write (entries : Entries) (name : String) (value : Option Callable) : Entries :=
  fun candidate => if candidate = name then value else entries candidate

/-- Static provenance advances through a successful definition, a direct
name copy, or a wrapper return. Call arguments are the existing bounded
read-only positional operands. -/
inductive Schedule (globals : List String) : Entries → List Command → Prop where
  | nil (entries : Entries) : Schedule globals entries []
  | define {entries : Entries} {body : Callable} {rest : List Command} :
      Visible globals body.name → body.Admitted globals →
      Schedule globals (entries.write body.name (some body)) rest →
      Schedule globals entries (body.command :: rest)
  | setup {entries : Entries} {name : String} {source : Expr} {rest : List Command} :
      Visible globals name → Initializer globals source → Schedule globals (entries.write name none) rest →
      Schedule globals entries (.assign name source :: rest)
  | copy {entries : Entries} {source destination : String} {body : Callable} {rest : List Command} :
      Visible globals source → Visible globals destination → entries source = some body →
      Schedule globals (entries.write destination (some body)) rest →
      Schedule globals entries (.assign destination (.scalar (.read source)) :: rest)
  | invoke {entries : Entries} {callee destination : String} {body : Callable}
      {arguments : List Expr} {rest : List Command} :
      Visible globals callee → Visible globals destination →
      entries callee = some body → (∀ argument ∈ arguments, Operand globals argument) →
      Schedule globals (entries.write destination body.returned) rest →
      Schedule globals entries (invocation callee destination arguments :: rest)

abbrev Profile (commands : List Command) : Prop := Schedule (names commands) (fun _ => none) commands

/-- The code table and runtime agree on a closure with saved positional
defaults. Aliases retain both its actual address and its saved values. -/
structure Saved (program : Program) (state : State) (name : String) (definition : Definition) where
  id : Nat
  codes : List Lowering.Expr
  address : Lists.Address
  values : List Value
  codeLength : codes.length = definition.parameters.optional.length
  valueLength : values.length = definition.parameters.optional.length
  found : program[id]? = some (definition.emitted codes)
  live : RootCall.Live state name address id [] false
    ((definition.parameters.optional.map (fileSlot ∘ Prod.fst)).zip values)

@[expose] def LiveBinding (globals : List String) (program : Program) (state : State)
    (name : String) : Callable → Prop
  | .required chain => Bindings.LiveBinding globals program state name chain
  | .defaulted definition => name ∈ globals ∧ Nonempty (Saved program state name definition)

@[expose] def LiveBindings (globals : List String) (program : Program) (entries : Entries) (state : State) : Prop :=
  ∀ name body, entries name = some body → LiveBinding globals program state name body

/-- Return reads the lexical parameter in the activation provided by
positional binding. The result keeps the exact heap after caller restore. -/
inductive ReturnsParameter (caller : State) (definition : Definition)
    (codes : List Lowering.Expr) (assigned : List (Binding × Value)) : Outcome Value → Prop where
  | read {value : Value}
      (read : (activate caller (definition.emitted codes) [] assigned).bindingValue (fileSlot definition.returned) = .ok value) :
      ReturnsParameter caller definition codes assigned
        (.ok value (restoreCaller caller (activate caller (definition.emitted codes) [] assigned)))
  | error {error : Lists.Error}
      (read : (activate caller (definition.emitted codes) [] assigned).bindingValue (fileSlot definition.returned) = .error error) :
      ReturnsParameter caller definition codes assigned
        (.error error (restoreCaller caller (activate caller (definition.emitted codes) [] assigned)))

/-- Independent source execution for an admitted call. The callee is read
before positional operands. Preparation starts only after all operands
succeed. The binder uses values saved at the closure's actual address. -/
inductive Calls (state : State) (definition : Definition) (codes : List Lowering.Expr) (saved : List Value)
    (arguments : List Expr) : Outcome Value → Prop where
  | rejected {actuals : List Value} {error : Lists.Error} :
      RootCall.EvaluatesOperands state arguments (.ok actuals state) →
      Trace.Defaults.Binds (definition.parameters.slots saved) actuals (.error error) →
      Calls state definition codes saved arguments (.error error state)
  | returned {actuals : List Value} {assigned : List (Binding × Value)} {out : Outcome Value} :
      RootCall.EvaluatesOperands state arguments (.ok actuals state) →
      Trace.Defaults.Binds (definition.parameters.slots saved) actuals (.ok assigned) →
      ReturnsParameter state definition codes assigned out →
      Calls state definition codes saved arguments out

inductive Step (resolved : ResolvedModule) (globals : List String) :
    Nat → State → Command → Modules.Result Unit → Prop where
  | ordinary {index : Nat} {state : State} {command : Command} {out : Modules.Result Unit} :
      Leaf.Step resolved globals index state command out → Step resolved globals index state command out
  | definition {index : Nat} {state : State} {command : Command} {out : Modules.Result Unit} :
      Trace.Defaults.Step resolved globals index state command out → Step resolved globals index state command out
  | call {index : Nat} {state : State} {callee destination : String} {definition : Definition}
      {arguments : List Expr} {actuals : List Lowering.Expr} {out : Outcome Value}
      (saved : Saved resolved.program state callee definition) :
      resolved.source.commands[index]? =
        some (.exec (.assignExpr destination (.call (Leaf.readOperand (globalSlot callee)) actuals [] none none))) →
      RootCall.Operand globals (.scalar (.read callee)) (Leaf.readOperand (globalSlot callee)) →
      Assignment.InOrder (RootCall.Operand globals) arguments actuals →
      Calls state definition saved.codes saved.values arguments out →
      Step resolved globals index state (invocation callee destination arguments) (Leaf.assignResult destination out)

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.WithDefaults
