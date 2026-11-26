module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Forwarding

open Assignment (LexicalBlock OperandInProfile RhsInProfile TargetInProfile)
open Block (LocalBinders)
open Functions (Body Declaration FreeName Program activate define)
open Lists (State Address)
open Functions.Lowering.Resolve (resolveTracked)

/-- Search outward, stopping at the first block which declares the name. -/
inductive Nearest (name : String) : List (List String) → Nat → Prop where
  | owns {owned : List String} {outer : List (List String)} :
      name ∈ owned → Nearest name (owned :: outer) 0
  | farther {owned : List String} {outer : List (List String)} {distance : Nat} :
      name ∉ owned → Nearest name outer distance → Nearest name (owned :: outer) (distance + 1)

/-- Each intermediate function only defines and returns the next function.
The innermost body is the mixed assignment and return from the capture theorem. -/
inductive Chain where
  | mixed (name : String) (parameters : List String) (body : MixedBody)
  | wrapper (name : String) (parameters : List String) (child : Chain)

@[expose] def Chain.name : Chain → String
  | .mixed name .. | .wrapper name .. => name

@[expose] def Chain.parameters : Chain → List String
  | .mixed _ parameters _ | .wrapper _ parameters _ => parameters

@[expose] def Chain.body : Chain → Statement
  | .mixed _ _ body => body.statement
  | .wrapper _ _ child =>
    .seq (.define child.name (.required child.parameters) child.body)
      (.ret (some (.scalar (.read child.name))))

@[expose] def Chain.definition (chain : Chain) : Statement :=
  .define chain.name (.required chain.parameters) chain.body

@[expose] def parentContext (globals : List String) (outer : List (List String)) : BlockContext :=
  ⟨⟨outer.flatten, globals⟩, .local⟩

/-- Acceptance evidence at the mixed body boundary. Capture selection is
specified separately by the declarative emission relation. -/
inductive Accepted (globals : List String) (program : Program) : List (List String) → Chain → Prop where
  | mixed {outer : List (List String)} {name : String} {parameters locals : List String} {body : MixedBody}
      {next : Program} {assignment : ResolvedPatternAssignment} {returned : Functions.Lowering.Expr}
      {returnReads : List Binding} :
      LocalBinders parameters [body.destination] locals →
      TargetInProfile .local body.target → RhsInProfile body.rhs → OperandInProfile body.returned →
      (do
        let layout ← collectFunctionLayout (parentContext globals outer).reads (.required parameters) body.statement
        elaboratePatternAssignment layout.block.reads layout.block.writes body.target body.rhs program) =
        .ok (assignment, next) →
      resolveTracked (childBlock (parentContext globals outer) parameters locals).context body.returned =
        .ok (returned, returnReads) →
      Accepted globals program outer (.mixed name parameters body)
  | wrapper {outer : List (List String)} {name : String} {parameters locals : List String} {child : Chain} :
      LocalBinders parameters [child.name] locals → child.name.toList.head? ≠ some '$' →
      Accepted globals program ((parameters ++ locals) :: outer) child →
      Accepted globals program outer (.wrapper name parameters child)

structure Frame where
  parameters : List String
  locals : List String
  free : List FreeName
  code : Body

@[expose] def Frame.owned (frame : Frame) : List String := frame.parameters ++ frame.locals

@[expose] def Frame.declaration (frame : Frame) : Declaration :=
  ⟨requiredSignature frame.parameters, frame.locals.map fileSlot, frame.free, frame.code⟩

/-- Capture plans in outer-to-inner order. A definition requests its child's
free references even when the wrapper body has no direct read of them. -/
inductive Emits (globals : List String) : List (List String) → Chain → List Frame → Prop where
  | mixed {outer : List (List String)} {name : String} {parameters locals : List String}
      {body : MixedBody} {reads : List Binding} {free : List FreeName} {code : Body} :
      LocalBinders parameters [body.destination] locals →
      BodyReads ⟨parameters ++ locals, outer.flatten, globals⟩ body.statement reads →
      Selects ⟨parameters ++ locals, outer.flatten, globals⟩ reads free →
      Emits globals outer (.mixed name parameters body) [⟨parameters, locals, free, code⟩]
  | wrapper {outer : List (List String)} {name : String} {parameters locals : List String} {child : Chain}
      {head : Frame} {tail : List Frame} {free : List FreeName} {code : Body} :
      LocalBinders parameters [child.name] locals →
      Emits globals ((parameters ++ locals) :: outer) child (head :: tail) →
      Selects ⟨parameters ++ locals, outer.flatten, globals⟩
        (head.free.map FreeName.source ++ [fileSlot child.name]) free →
      Emits globals outer (.wrapper name parameters child) (⟨parameters, locals, free, code⟩ :: head :: tail)

@[expose] def EmittedProgram (program : Program) : List Frame → Program
  | [] => program
  | frame :: child => (EmittedProgram program child).push frame.declaration

/-- Link each wrapper's definition instruction to its child's emitted ID.
The mixed leaf is the endpoint of the wrapper path. -/
inductive Links (seed : Program) : Chain → List Frame → Prop where
  | mixed (name : String) (parameters : List String) (body : MixedBody) (frame : Frame)
      (block : LexicalBlock) : LeafCode block body frame.code →
      Links seed (.mixed name parameters body) [frame]
  | wrapper {name : String} {parameters : List String} {child : Chain}
      {frame childFrame : Frame} {rest : List Frame} :
      child.name ∈ frame.owned →
      frame.code = .seq (.define (fileSlot child.name) (EmittedProgram seed rest).size)
        (.returnExpr (.atom (.read (.bound (fileSlot child.name))))) →
      Links seed child (childFrame :: rest) →
      Links seed (.wrapper name parameters child) (frame :: childFrame :: rest)

/-- The linked leaf uses the exact lexical scopes collected along the
emitted chain. The enclosing scopes are kept in nearest-first order. -/
inductive ScopedLeaves (globals : List String) : List (List String) → Chain → List Frame → Prop where
  | mixed {outer : List (List String)} {name : String} {params : List String} {body : MixedBody}
      {frame : Frame} :
      LeafCode ⟨frame.owned, outer.flatten, globals⟩ body frame.code →
      ScopedLeaves globals outer (.mixed name params body) [frame]
  | wrapper {outer : List (List String)} {name : String} {params : List String} {child : Chain}
      {frame : Frame} {rest : List Frame} :
      ScopedLeaves globals (frame.owned :: outer) child rest →
      ScopedLeaves globals outer (.wrapper name params child) (frame :: rest)

/-- Compiler capture entries use the same lexical name at each frame. -/
abbrev reference (binding : Binding) : FreeName := ⟨binding, binding⟩

/-- For a demand from the child, a parent forwards a global or a local
which it does not own. An owned local terminates this request. -/
@[expose] def Passes (parent child : Frame) : Prop :=
  ∀ binding, reference binding ∈ child.free →
    (reference binding ∈ parent.free ↔ binding.scope = .global ∨ binding.name ∉ parent.owned)

/-- A capture refers to its original name and lies outside the frame's
owned local slots. Global names use a distinct slot namespace. -/
@[expose] def Frame.WellScoped (frame : Frame) : Prop :=
  ∀ entry ∈ frame.free, ∃ binding, entry = reference binding ∧
    (binding.scope = .global ∨ binding.name ∉ frame.owned)

/-- Successful closure creation and activation along a path, using the
capture list stored in each newly created function cell. Arguments are
already bound to their slots. -/
inductive Invokes (program : Program) : State → List Frame → State → Prop where
  | nil (state : State) : Invokes program state [] state
  | step {state created final : State} {frame : Frame} {rest : List Frame}
      {id : Nat} {target : Binding} {captures : List Lists.Capture} {arguments : List (Binding × Lists.Value)} :
      program[id]? = some frame.declaration →
      Installs state frame.free captures →
      define program target id [] state = .ok .next created →
      created.heap[state.heap.size]? = some ⟨.function ⟨id, captures, []⟩, false⟩ →
      Invokes program (activate created frame.declaration captures arguments) rest final →
      Invokes program state (frame :: rest) final

/-- A source slot may own the address or have already captured it. -/
@[expose] def HasAddress (state : State) (binding : Binding) (address : Address) : Prop :=
  state.slots binding = some (.owned address) ∨
    state.slots binding = some (.captured address (binding.scope == .local))

/-- The route from a reference toward its nearest local owner, traversed
from the innermost declaration out. -/
inductive LocalRoute (name : String) (outer : List (List String)) : List Frame → Nat → Prop where
  | outside {distance : Nat} : Nearest name outer distance → LocalRoute name outer [] distance
  | owns {head : Frame} {tail : List Frame} : name ∈ head.owned →
      reference (fileSlot name) ∉ head.free → LocalRoute name outer (head :: tail) 0
  | forwards {head : Frame} {tail : List Frame} {distance : Nat} : name ∉ head.owned →
      reference (fileSlot name) ∈ head.free → LocalRoute name outer tail distance →
      LocalRoute name outer (head :: tail) (distance + 1)

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Forwarding
