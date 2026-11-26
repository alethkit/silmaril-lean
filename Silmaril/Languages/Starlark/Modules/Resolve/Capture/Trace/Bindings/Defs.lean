module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings

open Forwarding (Chain)

local notation "Expr" => Functions.Lowering.Resolve.SourceExpr

/-- Source provenance for names that may be called. A name records its body
shape, while live execution determines the actual closure and captures. -/
abbrev Environment := String → Option Chain

@[expose] def Environment.write (entries : Environment) (name : String) (body : Option Chain) : Environment :=
  fun candidate => if candidate = name then body else entries candidate

/-- A checked load-free module can interleave definitions, setup, aliases
and calls. On successful execution a wrapper introduces its child, and an
explicit name copy retains the referenced closure's provenance. -/
inductive Schedule (globals : List String) : Environment → List Command → Prop where
  | nil (entries : Environment) : Schedule globals entries []
  | define {entries : Environment} {chain : Chain} {rest : List Command} :
      Visible globals chain.name → Definitions globals [] chain →
      Schedule globals (entries.write chain.name (some chain)) rest →
      Schedule globals entries (root chain :: rest)
  | setup {entries : Environment} {name : String} {source : Expr} {rest : List Command} :
      Visible globals name → Initializer globals source → Schedule globals (entries.write name none) rest →
      Schedule globals entries (.assign name source :: rest)
  | copy {entries : Environment} {source destination : String} {chain : Chain} {rest : List Command} :
      Visible globals source → Visible globals destination → entries source = some chain →
      Schedule globals (entries.write destination (some chain)) rest →
      Schedule globals entries (.assign destination (.scalar (.read source)) :: rest)
  | wrapper {entries : Environment} {name callee destination : String} {parameters : List String}
      {child : Chain} {arguments : List Expr} {rest : List Command} :
      Visible globals callee → Visible globals destination →
      entries callee = some (.wrapper name parameters child) → (∀ arg ∈ arguments, Operand globals arg) →
      Schedule globals (entries.write destination (some child)) rest →
      Schedule globals entries (invocation callee destination arguments :: rest)
  | leaf {entries : Environment} {name callee destination : String} {parameters : List String}
      {body : MixedBody} {arguments : List Expr} {rest : List Command} :
      Visible globals callee → Visible globals destination →
      entries callee = some (.mixed name parameters body) → (∀ arg ∈ arguments, Operand globals arg) →
      Schedule globals (entries.write destination none) rest →
      Schedule globals entries (invocation callee destination arguments :: rest)

abbrev Profile (commands : List Command) : Prop := Schedule (names commands) (fun _ => none) commands

/-- Evidence attached to a callable closure shape in the final linked table.
It says where the code was emitted and how its defining scopes were collected. -/
structure CallableCode (globals : List String) (program : Functions.Program) (chain : Chain)
    (seed : Functions.Program) (frame : Forwarding.Frame) (rest : List Forwarding.Frame) : Prop where
  linked : Forwarding.Links seed chain (frame :: rest)
  retained : Wrapper.KeepsTable seed program (frame :: rest)
  lexical : ∃ (outer : List (List String)) (enclosing : List String),
    (∀ name, name ∈ outer.flatten ↔ name ∈ enclosing) ∧ Definitions globals enclosing chain ∧
      Forwarding.Emits globals outer chain (frame :: rest) ∧ Forwarding.ScopedLeaves globals outer chain (frame :: rest)

/-- The object and captures are read from the reached state. The code
certificate describes the closure's origin in the final declaration table. -/
@[expose] def LiveBinding (globals : List String) (program : Functions.Program) (state : Lists.State)
    (name : String) (chain : Chain) : Prop :=
  name ∈ globals ∧
    ∃ (seed : Functions.Program) (frame : Forwarding.Frame) (rest : List Forwarding.Frame) (address : Nat) (captures : List Lists.Capture),
      CallableCode globals program chain seed frame rest ∧
      RootCall.Live state name address (Forwarding.EmittedProgram seed rest).size captures false ∧
      (∃ owner, Installs owner frame.free captures) ∧
      (∀ entry ∈ captures, entry.binding.name.toList.head? ≠ some '$')

/-- Every tracked name at a reached prefix reads its actual live closure.
Several names may hold the same address, and separate activations of the
same source definition may hold different addresses and capture lists. -/
@[expose] def LiveBindings (globals : List String) (program : Functions.Program) (entries : Environment)
    (state : Lists.State) : Prop :=
  ∀ name chain, entries name = some chain → LiveBinding globals program state name chain

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings
