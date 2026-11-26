module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Block.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published

open Assignment (LexicalBlock)
open Defaults
open Defaults.Nested.Sequence.Recursive (Site KeywordLexical Emissions)
open Defaults.Nested.Sequence.Recursive.Call (ClosureAt Arguments)
open Defaults.Nested.Sequence.Recursive.Call.Suite (Runs)
open Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance (Elaborates empty)
open Functions
open Lists (State Outcome Capture)
open Lists.Iteration (Flow)

local notation "Expr" => Lowering.Resolve.SourceExpr

@[expose] def moduleLex (globals : List String) : LexicalBlock := ⟨[], [], globals⟩

/-- A root links the independent definition layout to the suite's ordered
emissions. Its own index follows those emitted by its body. -/
structure Root (globals : List String) where
  keywords : List PlainKeywordParameter
  varargs : Option String
  kwargs : Option String
  site : Site (moduleLex globals) keywords varargs kwargs .global
  lexical : KeywordLexical (moduleLex globals) keywords
  seed : Program
  bodyTable : Program
  children : Emissions
  suite : Elaborates site.block empty site.source seed site.body bodyTable children

@[expose] def Root.command {globals : List String} (root : Root globals) : Command :=
  .define root.site.name root.site.sourceSignature root.site.source

@[expose] def Root.id {globals : List String} (root : Root globals) : DeclarationId := root.bodyTable.size

@[expose] def Root.table {globals : List String} (root : Root globals) : Program :=
  root.bodyTable.push root.site.declaration

abbrev Environment (globals : List String) := String → Option (Root globals)

@[expose] def update {globals : List String} (env : Environment globals) (name : String)
    (root : Option (Root globals)) : Environment globals :=
  fun candidate => if candidate = name then root else env candidate

/-- Ordinary expressions clear the destination's provenance. An explicit
copy transfers the root certificate without assuming the closure's address. -/
inductive Tracks {globals : List String} (env : Environment globals) :
    Expr → Lowering.Expr → Option (Root globals) → Prop where
  | forget {source code} : Tracks env source code none
  | copy {name : String} {root : Root globals} :
      env name = some root →
      Tracks env (.scalar (.read name)) (Leaf.readOperand (globalSlot name)) (some root)

structure Invocation (globals : List String) where
  callee : String
  calleeGlobal : callee ∈ globals
  legal : callee.toList.head? ≠ some '$'
  destination : String
  destinationGlobal : destination ∈ globals
  arguments : List Expr
  codes : List Lowering.Expr
  reads : List Binding
  operands : Arguments (moduleLex globals) arguments codes reads
  keywords : Defaults.Nested.Sequence.Recursive.Call.Named.Operands (moduleLex globals)
  star : Option (Defaults.Nested.Sequence.Recursive.Call.Named.Spread (moduleLex globals)) := none
  mapping : Option (Defaults.Nested.Sequence.Recursive.Call.Named.Mapping (moduleLex globals)) := none

open Defaults.Nested.Sequence.Recursive.Call.Named (Spread Mapping expressionAt RunsAt)

@[expose] def Invocation.source {globals : List String} (call : Invocation globals) : Command :=
  .assign call.destination (.call (.scalar (.read call.callee)) call.arguments call.keywords.source
    (call.star.map Spread.source) (call.mapping.map Mapping.source))

@[expose] def Invocation.code {globals : List String} (call : Invocation globals) : Lowering.Expr :=
  expressionAt (globalSlot call.callee) call.codes call.keywords.codes
    (call.star.map Spread.code) (call.mapping.map Mapping.code)

/-- The load-free schedule threads declaration tables and provenance in
source order. Ordinary assignments and calls can be interleaved. -/
inductive Plan (globals : List String) :
    Environment globals → List Command → Program → List Modules.Command → Program → Prop where
  | done {env seed} : Plan globals env [] seed [] seed
  | define {env source code final} (root : Root globals) :
      Plan globals (update env root.site.name (some root)) source root.table code final →
      Plan globals env (root.command :: source) root.seed (.exec (.define root.site.name root.id) :: code) final
  | assign {env name source code reads track rest next seed final} :
      name ∈ globals → Body.Operand (moduleLex globals) source code reads →
      Tracks env source code track → Plan globals (update env name track) rest seed next final →
      Plan globals env (.assign name source :: rest) seed (.exec (.assignExpr name code) :: next) final
  | invoke {env rest next seed final} (call : Invocation globals) (root : Root globals) :
      env call.callee = some root → Plan globals (update env call.destination none) rest seed next final →
      Plan globals env (call.source :: rest) seed (.exec (.assignExpr call.destination call.code) :: next) final

/-- Module roots and aliases point at records in the reached shared heap.
An activation can read captured module slots even when they are uninitialized. -/
@[expose] def Live {globals : List String} (env : Environment globals) (state : State) : Prop :=
  ∀ name root, env name = some root →
    ∃ address defining, state.bindingValue (globalSlot name) = .ok (.function address) ∧
      Nonempty (ClosureAt root.site root.id defining state address)

@[expose] def afterWrite (name : String) : Outcome Lists.Value → Modules.Result Unit
  | .error error state => .error (.runtime error) state
  | .ok value state => .ok () (state.write (globalSlot name) value)

inductive Executes (globals : List String) : State → Command → Modules.Result Unit → Prop where
  | define {state : State} (root : Root globals) (captures : List Capture) {out : Outcome Flow} :
      Installs state root.site.free captures →
      Lexical.DefinesFor (moduleLex globals) (globalSlot root.site.name) root.id root.site.free
        root.site.defaultKeys root.site.defaultsInOrder state out →
      Executes globals state root.command (Modules.afterCode out)
  | assign {state name source code out} :
      Body.Evaluates (moduleLex globals) state source code out →
      Executes globals state (.assign name source) (afterWrite name out)
  | invoke {state out} (call : Invocation globals) (root : Root globals) :
      RunsAt root.site (fun active result => Runs root.site.block active root.site.source root.site.body.code result)
        (moduleLex globals) root.id call.callee (globalSlot call.callee)
        call.arguments call.codes call.keywords.source call.keywords.codes call.star call.mapping state out →
      Executes globals state call.source (afterWrite call.destination out)

/-- Stop at the first reached error, retaining its exact state. -/
inductive ExecutesAll (globals : List String) : State → List Command → Modules.Result Unit → Prop where
  | done (state : State) : ExecutesAll globals state [] (.ok () state)
  | step {state middle first rest out} :
      Executes globals state first (.ok () middle) → ExecutesAll globals middle rest out →
      ExecutesAll globals state (first :: rest) out
  | failed {state final first rest error} :
      Executes globals state first (.error error final) → ExecutesAll globals state (first :: rest) (.error error final)

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
