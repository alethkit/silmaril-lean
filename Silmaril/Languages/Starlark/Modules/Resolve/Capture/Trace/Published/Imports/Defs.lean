module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Defs
public import Silmaril.Languages.Starlark.Modules.Loader.Operational.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports

open Assignment (LexicalBlock)
open Defaults
open Defaults.Nested.Sequence.Recursive.Call (Arguments)
open Defaults.Nested.Sequence.Recursive.Call.Named (Mapping Operands RunsAt Spread expressionAt)
open Functions
open Lists (State Outcome)
open Loader (Manifest Session)

local notation "Expr" => Lowering.Resolve.SourceExpr

@[expose] def block (alias destination tail : String) : LexicalBlock :=
  ⟨[alias], [], [destination, tail]⟩

/-- One renamed import, a call through its file-local slot and one ordinary
assignment. Both global names participate in whole-module lexical resolution. -/
structure Consumer where
  label : String
  name : String
  alias : String
  destination : String
  tail : String
  legal : alias.toList.head? ≠ some '$'
  publicName : Modules.isPublic name = true
  arguments : List Expr
  codes : List Lowering.Expr
  reads : List Binding
  operands : Arguments (block alias destination tail) arguments codes reads
  keywords : Operands (block alias destination tail)
  star : Option (Spread (block alias destination tail)) := none
  mapping : Option (Mapping (block alias destination tail)) := none
  rhs : Expr
  rhsCode : Lowering.Expr
  rhsReads : List Binding
  suffix : Body.Operand (block alias destination tail) rhs rhsCode rhsReads

@[expose] def Consumer.item (plan : Consumer) : Modules.Import :=
  ⟨plan.name, plan.alias⟩

@[expose] def Consumer.call (plan : Consumer) : Expr :=
  .call (.scalar (.read plan.alias)) plan.arguments plan.keywords.source
    (plan.star.map Spread.source) (plan.mapping.map Mapping.source)

@[expose] def Consumer.callCode (plan : Consumer) : Lowering.Expr :=
  expressionAt (fileSlot plan.alias) plan.codes plan.keywords.codes
    (plan.star.map Spread.code) (plan.mapping.map Mapping.code)

@[expose] def Consumer.commands (plan : Consumer) : List Command :=
  [.load plan.label [plan.item], .assign plan.destination plan.call, .assign plan.tail plan.rhs]

@[expose] def Consumer.code (plan : Consumer) : List Modules.Command :=
  [.load plan.label [plan.item], .exec (.assignExpr plan.destination plan.callCode),
    .exec (.assignExpr plan.tail plan.rhsCode)]

/-- Producer zero has no dependencies. Consumer one has just the one
requester-relative label. Both use the producer's emitted table. -/
@[expose] def graph (producer consumer : ResolvedModule) (plan : Consumer) : Manifest :=
  #[⟨producer.source, []⟩, ⟨consumer.source, [(plan.label, 0)]⟩]

/-- The source profile tracks either a producer export or a name outside the
producer's declared globals. The consumer supplies no declaration or address. -/
@[expose] def Covered (exports : Environment) (producer : List Command) (plan : Consumer) : Prop :=
  (exports plan.name).isSome ∨ plan.name ∉ Trace.names producer

@[expose] def reachedSession {α : Type} : Loader.Result α → Session
  | .ok _ s | .error _ s => s

/-- Use module publication, with the loader's error attribution and success
cache. This observation is shared by the independent source rules. -/
@[expose] def observed (id : Loader.ModuleId) (source : Modules.Source) (caller : State)
    (cache : List (Loader.ModuleId × Modules.Published)) (out : Modules.Result Unit) :
    Loader.Result Modules.Published :=
  match Modules.finish source caller out with
  | .error error final => .error (.initialization id error) ⟨final, cache⟩
  | .ok published final => .ok published ⟨final, (id, published) :: cache⟩

/-- A cache hit reuses the published value and the exact runtime heap. -/
inductive Producer (commands : List Command) (source : Modules.Source) :
    Session → Loader.Result Modules.Published → Prop where
  | cold {state : Session} {out : Modules.Result Unit} :
      state.cache.lookup 0 = none →
      ExecutesAll (Trace.names commands) (Modules.enter source state.runtime) commands out →
      Producer commands source state (observed 0 source state.runtime state.cache out)
  | cached {state : Session} {published : Modules.Published} :
      state.cache.lookup 0 = some published →
      Producer commands source state (.ok published state)

/-- Look up the requested name before any caller operand runs. -/
inductive BindsAlias (plan : Consumer) (published : Modules.Published) (state : State) :
    Modules.Result Unit → Prop where
  | missing : published.exports.lookup plan.name = none →
      BindsAlias plan published state (.error (.missingExport plan.label plan.name) state)
  | found {value : Lists.Value} : published.exports.lookup plan.name = some value →
      BindsAlias plan published state (.ok () (state.write (fileSlot plan.alias) value))

/-- Evaluate in the restored importer frame. A call error skips the
assignment and suffix. The suffix sees the successful assignment. -/
inductive Tail (plan : Consumer) (callee : Callable) (state : State) : Modules.Result Unit → Prop where
  | callError {error : Lists.Error} {final : State} :
      RunsAt callee.site callee.BodyRuns (block plan.alias plan.destination plan.tail)
        callee.id plan.alias (fileSlot plan.alias) plan.arguments plan.codes
        plan.keywords.source plan.keywords.codes plan.star plan.mapping state (.error error final) →
      Tail plan callee state (.error (.runtime error) final)
  | called {value : Lists.Value} {returned : State} {suffix : Outcome Lists.Value} :
      RunsAt callee.site callee.BodyRuns (block plan.alias plan.destination plan.tail)
        callee.id plan.alias (fileSlot plan.alias) plan.arguments plan.codes
        plan.keywords.source plan.keywords.codes plan.star plan.mapping state (.ok value returned) →
      Body.Evaluates (block plan.alias plan.destination plan.tail)
        (returned.write (globalSlot plan.destination) value) plan.rhs plan.rhsCode suffix →
      Tail plan callee state (afterWrite plan.tail suffix)

inductive Runs (commands : List Command) (producer consumer : Modules.Source)
    (plan : Consumer) (exports : Environment) (caller : Session) :
    Loader.Result Modules.Published → Prop where
  | producerError {error : Loader.Error} {reached : Session} :
      Producer commands producer { caller with runtime := Modules.enter consumer caller.runtime }
        (.error error reached) →
      Runs commands producer consumer plan exports caller
        (.error error { reached with runtime := Modules.restoreThread caller.runtime reached.runtime })
  | missing {published : Modules.Published} {reached : Session} {error : Modules.Error} :
      Producer commands producer { caller with runtime := Modules.enter consumer caller.runtime }
        (.ok published reached) →
      BindsAlias plan published reached.runtime (.error error reached.runtime) →
      Runs commands producer consumer plan exports caller
        (observed 1 consumer caller.runtime reached.cache (.error error reached.runtime))
  | called {published : Modules.Published} {reached : Session} {bound : State}
      {callee : Callable} {out : Modules.Result Unit} :
      Producer commands producer { caller with runtime := Modules.enter consumer caller.runtime }
        (.ok published reached) →
      BindsAlias plan published reached.runtime (.ok () bound) →
      exports plan.name = some callee →
      Tail plan callee bound out →
      Runs commands producer consumer plan exports caller (observed 1 consumer caller.runtime reached.cache out)

abbrev Agrees (commands : List Command) (producer consumer : ResolvedModule)
    (plan : Consumer) (exports : Environment) (caller : Session) : Prop :=
  ∃ out, Runs commands producer.source consumer.source plan exports caller out ∧
    Loader.Runs producer.program (graph producer consumer plan) [] (.initialize 1) caller out ∧
    Loader.load producer.program (graph producer consumer plan) 1 caller = out

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
