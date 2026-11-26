module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Wrapper.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Leaf

open Assignment (LexicalBlock ReadResolves)
open Lists (State Outcome)
open Lists.Iteration (Flow UnpacksValue)
open Functions

local notation "Value" => Lists.Value

/-- Lexical plan for a plain RHS and a two-leaf mixed assignment. Every
operand in this increment is a normalized identifier read. -/
structure Plan where
  destination : Binding
  rhs : Binding
  receiver : Binding
  index : Binding
  returned : Binding

/-- Names reserved by the compiler are unavailable to the source profile. -/
@[expose] def Plan.Legal (plan : Plan) : Prop :=
  ∀ binding ∈ [plan.destination, plan.rhs, plan.receiver, plan.index, plan.returned],
    binding.name.toList.head? ≠ some '$'

/-- A source frame has no owned or captured slots at compiler-private names. -/
@[expose] def noPrivateSlots (state : State) : Prop :=
  ∀ binding, binding.name.toList.head? = some '$' → state.slots binding = none

/-- The left leaf is a local name. Receiver and index are reads in that
same lexical block, so either can observe the first leaf's write. -/
inductive Resolves (block : LexicalBlock) : MixedBody → Plan → Prop where
  | reads (destination rhs receiver index returned : String) (right collection offset result : Binding) :
      ReadResolves block rhs (.atom (.read (.bound right))) [right] →
      ReadResolves block receiver (.atom (.read (.bound collection))) [collection] →
      ReadResolves block index (.atom (.read (.bound offset))) [offset] →
      ReadResolves block returned (.atom (.read (.bound result))) [result] →
      Resolves block
        ⟨destination, .scalar (.read receiver), .scalar (.read index), .plain (.scalar (.read rhs)),
          .scalar (.read returned)⟩
        ⟨fileSlot destination, right, collection, offset, result⟩

@[expose] def readOperand (binding : Binding) : Lowering.Expr := .atom (.read (.bound binding))

/-- Resolved code emitted for this leaf. The source execution rules below
work directly on names, the ordered leaves, and the shared store. -/
@[expose] def Plan.code (plan : Plan) : Functions.Body :=
  .seq (Functions.Comprehensions.assignPatternCode
      (.sequence [.name plan.destination, .subscript (readOperand plan.receiver) (readOperand plan.index)])
      (.plain (readOperand plan.rhs)) Functions.Comprehensions.directStages)
    (.returnExpr (readOperand plan.returned))

/-- The source store checks its receiver, then its index, then performs
the heap update. It starts after the name leaf has been assigned. -/
@[expose] def store (plan : Plan) (value : Value) (state : State) : Outcome Unit :=
  (state.read (.bound plan.receiver)).resume fun receiver middle =>
    (middle.read (.bound plan.index)).resume fun index next =>
      Lists.writeIndex receiver index value next

/-- Independent execution of the bounded mixed assignment and return.
An unpack is checked before writes. Later failure keeps completed writes. -/
inductive Runs (plan : Plan) (state : State) : Outcome Flow → Prop where
  | rhsError {error : Lists.Error} :
      state.bindingValue plan.rhs = .error error → Runs plan state (.error error state)
  | unpackError {rhs : Value} {error : Lists.Error} :
      state.bindingValue plan.rhs = .ok rhs →
      UnpacksValue state rhs 2 (.error error state) →
      Runs plan state (.error error state)
  | leaves {rhs first second : Value} :
      state.bindingValue plan.rhs = .ok rhs →
      UnpacksValue state rhs 2 (.ok [first, second] state) →
      Runs plan state
        ((store plan second (state.write plan.destination first)).resume fun () next =>
          (next.read (.bound plan.returned)).resume fun value => pure (.returned value))

/-- Observe a returned value or body error after restoring the caller. -/
@[expose] def returnTo (caller : State) : Outcome Flow → Outcome Value
  | .ok flow state => .ok (Lowering.callValue flow) (restoreCaller caller state)
  | .error error state => .error error (restoreCaller caller state)

/-- Runtime body choices for this normalized module profile. The wrapper
uses its source closure-return rule. The leaf uses its lexical plan and
the independent ordered assignment and return rules. -/
inductive BodyRuns (program : Program) (caller : State) (frame : Forwarding.Frame)
    (captures : List Lists.Capture) (assigned : List (Binding × Value)) : Outcome Value → Prop where
  | wrapper {seed : Program} {name : String} {parameters : List String} {child : Forwarding.Chain}
      {childFrame : Forwarding.Frame} {rest : List Forwarding.Frame}
      {selected : List Lists.Capture} {address : Lists.Address} {next : State} :
      Forwarding.Links seed (.wrapper name parameters child) (frame :: childFrame :: rest) →
      Wrapper.KeepsTable seed program (frame :: childFrame :: rest) →
      Wrapper.ReturnsChild seed caller child frame childFrame rest captures assigned selected
        (.ok (.function address) next) →
      BodyRuns program caller frame captures assigned (.ok (.function address) next)
  | leaf {block : LexicalBlock} {source : MixedBody} {plan : Plan} {out : Outcome Flow} :
      LeafCode block source frame.code → Resolves block source plan → plan.Legal →
      (∀ name ∈ frame.owned, name.toList.head? ≠ some '$') →
      (∀ capture ∈ captures, capture.binding.name.toList.head? ≠ some '$') →
      Runs plan (activate caller frame.declaration captures assigned) out →
      BodyRuns program caller frame captures assigned (returnTo caller out)

local notation "Operand" => Lowering.Resolve.SourceExpr

/-- A reached initializer operand for this profile. Displays allocate
after their elements have been evaluated, in source order. -/
inductive Setup (globals : List String) : State → Operand → Lowering.Expr → Outcome Value → Prop where
  | atom {state : State} {source : Operand} {code : Lowering.Expr} {out : Outcome Value} :
      RootCall.Operand globals source code → RootCall.Evaluates state source out →
      Setup globals state source code out
  | list {state : State} {items : List Operand} {codes : List Lowering.Expr} {out : Outcome (List Value)} :
      Assignment.InOrder (RootCall.Operand globals) items codes → RootCall.EvaluatesOperands state items out →
      Setup globals state (.list items) (.list codes) (Outcome.resume out Lists.allocate)
  | tuple {state : State} {items : List Operand} {codes : List Lowering.Expr} {out : Outcome (List Value)} :
      Assignment.InOrder (RootCall.Operand globals) items codes → RootCall.EvaluatesOperands state items out →
      Setup globals state (.tuple items) (.tuple codes) (Outcome.resume out Lists.allocateTuple)

/-- Commit the named destination after a successful source value only. -/
@[expose] def assignResult (destination : String) : Outcome Value → Modules.Result Unit
  | .ok value state => .ok () (state.write (globalSlot destination) value)
  | .error error state => .error (.runtime error) state

/-- Static command positions and runtime source judgments for the module
profile. Dynamic premises use the independent setup, argument, wrapper,
and leaf rules, together with the live closure cell from the shared store. -/
inductive Step (resolved : ResolvedModule) (globals : List String) :
    Nat → State → Command → Modules.Result Unit → Prop where
  | define {index : Nat} {state : State} {name : String} {parameters : List String}
      {body : Statement} {id : Nat} {frame : Forwarding.Frame} {captures : List Lists.Capture} :
      resolved.source.commands[index]? = some (.exec (.define name id)) →
      resolved.program[id]? = some frame.declaration → Installs state frame.free captures →
      Step resolved globals index state (.define name (.required parameters) body)
        (.ok () (State.write { state with heap := state.heap.push ⟨.function ⟨id, captures, []⟩, false⟩ }
          (globalSlot name) (.function state.heap.size)))
  | setup {index : Nat} {state : State} {name : String} {source : Operand} {code : Lowering.Expr}
      {out : Outcome Value} :
      resolved.source.commands[index]? = some (.exec (.assignExpr name code)) →
      Setup globals state source code out →
      Step resolved globals index state (.assign name source) (assignResult name out)
  | operandError {index : Nat} {state final : State} {destination : String} {callee : Operand}
      {positional : List Operand} {function : Lowering.Expr} {actuals : List Lowering.Expr}
      {error : Lists.Error} :
      resolved.source.commands[index]? = some (.exec (.assignExpr destination (.call function actuals [] none none))) →
      RootCall.Operand globals callee function →
      Assignment.InOrder (RootCall.Operand globals) positional actuals →
      RootCall.EvaluatesOperands state (callee :: positional) (.error error final) →
      Step resolved globals index state (.assign destination (.call callee positional [] none none))
        (.error (.runtime error) final)
  | call {index id : Nat} {state : State} {name destination : String}
      {positional : List Operand} {actuals : List Lowering.Expr} {values : List Value}
      {frame : Forwarding.Frame} {address : Lists.Address} {captures : List Lists.Capture} {frozen : Bool}
      {binding : Except Lists.Error (List (Binding × Value))} {out : Outcome Value} :
      resolved.source.commands[index]? =
        some (.exec (.assignExpr destination (.call (readOperand (globalSlot name)) actuals [] none none))) →
      RootCall.Operand globals (.scalar (.read name)) (readOperand (globalSlot name)) →
      Assignment.InOrder (RootCall.Operand globals) positional actuals →
      RootCall.EvaluatesOperands state positional (.ok values state) →
      state.bindingValue (globalSlot name) = .ok (.function address) →
      state.heap[address]? = some ⟨.function ⟨id, captures, []⟩, frozen⟩ →
      resolved.program[id]? = some frame.declaration →
      Entry.Binds frame.parameters values binding →
      (match binding with
       | .error error => out = .error error state
       | .ok assigned => BodyRuns resolved.program state frame captures assigned out) →
      Step resolved globals index state (.assign destination (.call (.scalar (.read name)) positional [] none none))
        (assignResult destination out)

/-- Collect the values of initialized declared globals in declaration order. -/
inductive Globals (state : State) : List String → List (String × Value) → Prop where
  | nil : Globals state [] []
  | initialized {name : String} {names : List String} {value : Value} {rest : List (String × Value)} :
      state.bindingValue (globalSlot name) = .ok value → Globals state names rest →
      Globals state (name :: names) ((name, value) :: rest)
  | absent {name : String} {names : List String} {error : Lists.Error} {rest : List (String × Value)} :
      state.bindingValue (globalSlot name) = .error error → Globals state names rest →
      Globals state (name :: names) rest

/-- Failure restores the caller with the exact residual heap and has
no publication. Success exports public initialized names and freezes
everything reachable from all initialized globals. -/
inductive Finishes (names : List String) (caller : State) :
    Modules.Result Unit → Modules.Result Modules.Published → Prop where
  | failed {state : State} {error : Modules.Error} :
      Finishes names caller (.error error state) (.error error { caller with heap := state.heap })
  | published {state : State} {values : List (String × Value)} {heap : Lists.Heap} :
      Globals state names values →
      Lists.Freezes state.heap (values.filterMap fun (_, value) => value.address?) heap →
      Finishes names caller (.ok () state)
        (.ok ⟨values.filter (fun (name, _) => Modules.isPublic name)⟩ { caller with heap })

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Leaf
