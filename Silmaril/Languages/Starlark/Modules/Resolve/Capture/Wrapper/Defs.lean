module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall.Defs
public import Silmaril.Languages.Starlark.Functions.Operational.Defs
public import Silmaril.Languages.Starlark.Functions.Denotation.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Wrapper

open Functions (Program activate restoreCaller)
open Forwarding (Chain EmittedProgram)
open Lists (Address Capture State Outcome)

local notation "Value" => Lists.Value

/-- A wrapper installs its child and binds the child's lexical name.
The allocated heap cell contains the selected addresses. -/
@[expose] def installChild (active : State) (name : String) (id : Nat) (captures : List Capture) : State :=
  let cell : Lists.Cell := ⟨.function ⟨id, captures, []⟩, false⟩
  { active with heap := active.heap.push cell }.write (fileSlot name) (.function active.heap.size)

/-- A closure remains callable if its cell still holds the declaration and
the capture list originally installed by its defining frame. -/
structure ClosureAt (state : State) (address : Address) (id : Nat) (frame : Forwarding.Frame)
    (captures : List Capture) (frozen : Bool) : Prop where
  cell : state.heap[address]? = some ⟨.function ⟨id, captures, []⟩, frozen⟩
  environment : ∃ owner, Installs owner frame.free captures

/-- The body step for a source wrapper. The only statement after the
definition is the lexical read that returns the newly allocated child. -/
inductive ReturnsChild (seed : Program) (caller : State) (child : Chain) (frame childFrame : Forwarding.Frame)
    (rest : List Forwarding.Frame) (captures : List Capture) (assigned : List (Binding × Value)) :
    List Capture → Outcome Value → Prop where
  | returns {selected : List Capture} :
      Installs (activate caller frame.declaration captures assigned) childFrame.free selected →
      ReturnsChild seed caller child frame childFrame rest captures assigned selected
        (.ok (.function (activate caller frame.declaration captures assigned).heap.size)
          (restoreCaller caller (installChild (activate caller frame.declaration captures assigned)
            child.name (EmittedProgram seed rest).size selected)))

/-- Starting with an escaped closure, follow zero or more wrapper returns.
The operands here are already evaluated. A binding error stops the path.
A mixed leaf is an endpoint and its body is separate. -/
inductive Walk (seed : Program) : State → Chain → List Forwarding.Frame → Address → List Capture →
    List (List Value) → Outcome Value → Prop where
  | stop {state : State} {chain : Chain} {frame : Forwarding.Frame} {rest : List Forwarding.Frame}
      {address : Address} {captures : List Capture} :
      Walk seed state chain (frame :: rest) address captures [] (.ok (.function address) state)
  | arity {state : State} {name : String} {params : List String} {child : Chain}
      {frame childFrame : Forwarding.Frame} {rest : List Forwarding.Frame} {address : Address} {captures : List Capture}
      {values : List Value} {remaining : List (List Value)} {error : Lists.Error} :
      Entry.Binds frame.parameters values (.error error) →
      Walk seed state (.wrapper name params child) (frame :: childFrame :: rest) address captures
        (values :: remaining) (.error error state)
  | step {state next : State} {name : String} {params : List String} {child : Chain}
      {frame childFrame : Forwarding.Frame} {rest : List Forwarding.Frame} {address nextAddress : Address}
      {captures selected : List Capture} {values : List Value} {assigned : List (Binding × Value)}
      {remaining : List (List Value)} {out : Outcome Value} :
      Entry.Binds frame.parameters values (.ok assigned) →
      ReturnsChild seed state child frame childFrame rest captures assigned selected (.ok (.function nextAddress) next) →
      Walk seed next child (childFrame :: rest) nextAddress selected remaining out →
      Walk seed state (.wrapper name params child) (frame :: childFrame :: rest) address captures
        (values :: remaining) out

/-- The number of define-and-return wrappers before the mixed leaf. -/
@[expose] def wrapperCount : Chain → Nat
  | .mixed .. => 0
  | .wrapper _ _ child => wrapperCount child + 1

/-- The corresponding sequence of resolved calls. Each return restores the
caller before the next, separate invocation. The terminal success retains
the heap cell of the closure that escaped. -/
inductive NativeWalk (program : Program) : State → Address → List (List Value) → Outcome Value → Prop where
  | stop {state : State} {address : Address} {closure : Lists.Closure} {frozen : Bool} :
      state.heap[address]? = some ⟨.function closure, frozen⟩ →
      NativeWalk program state address [] (.ok (.function address) state)
  | rejected {state : State} {address : Address} {values : List Value} {remaining : List (List Value)}
      {error : Lists.Error} :
      Functions.prepareExpanded program (List.range program.size) ⟨values, []⟩ (.function address) state =
        .error error state →
      NativeWalk program state address (values :: remaining) (.error error state)
  | returned {state active final : State} {address nextAddress : Address}
      {values : List Value} {remaining : List (List Value)} {out : Outcome Value}
      {plan : Functions.Prepared (List.range program.size)} :
      Functions.prepareExpanded program (List.range program.size) ⟨values, []⟩ (.function address) state =
        .ok (.closure plan) active →
      Functions.Exec program (Functions.withoutDeclaration (List.range program.size) plan.id) active plan.body
        (.ok (.returned (.function nextAddress)) final) →
      NativeWalk program (restoreCaller state final) nextAddress remaining out →
      NativeWalk program state address (values :: remaining) out

/-- Compose the existing value-level call denotation over already evaluated
actuals. Each invocation begins after restoration of the caller's frame. -/
@[expose] def denoteWalk (program : Program) : List (List Value) → Value → Lists.Meaning Value
  | [], callee => pure callee
  | values :: remaining, callee => fun state =>
    let available := List.range program.size
    let body (plan : Functions.Prepared available) :=
      Functions.denoteBody program (Functions.withoutDeclaration available plan.id) plan.body
    let out := Functions.Lowering.denoteDispatchWith program available body callee ⟨values, []⟩ state
    Outcome.resume out (denoteWalk program remaining)

/-- The final program retains the lookup results for the emitted chain. -/
@[expose] def KeepsTable (seed program : Program) (frames : List Forwarding.Frame) : Prop :=
  ∀ (index : Nat) (declaration : Functions.Declaration), (EmittedProgram seed frames)[index]? = some declaration →
    program[index]? = some declaration

/-- Each independent source step is matched at its actual command index.
A reached error terminates without claiming execution of the suffix. -/
inductive ReachedPrefix {SourceCommand : Type}
    (step : Nat → State → SourceCommand → Modules.Result Unit → Prop) :
    Nat → State → List SourceCommand → Modules.Result Unit → Prop where
  | nil {index : Nat} {state : State} : ReachedPrefix step index state [] (.ok () state)
  | next {index : Nat} {state next : State} {command : SourceCommand}
      {rest : List SourceCommand} {out : Modules.Result Unit} :
      step index state command (.ok () next) →
      ReachedPrefix step (index + 1) next rest out →
      ReachedPrefix step index state (command :: rest) out
  | error {index : Nat} {state final : State} {command : SourceCommand} {rest : List SourceCommand}
      {error : Modules.Error} :
      step index state command (.error error final) →
      ReachedPrefix step index state (command :: rest) (.error error final)

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Wrapper
