module

public import Silmaril.Languages.Starlark.Modules.Resolve.Block.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture

open Assignment (AssignmentResolves InOrder LexicalBlock OperandResolves RhsResolves TargetResolves)
open Functions (FreeName)
open Lists (State Address)

local notation "Operand" => Functions.Lowering.Resolve.SourceExpr

inductive Origin where
  | owned | enclosing | module

/-- Classify the resolved read against the current block and its enclosing
names. Forwarding additionally identifies the nearest owner in that chain. -/
inductive ReadOrigin (block : LexicalBlock) : Binding → Origin → Prop where
  | owned {name : String} : name ∈ block.owned → ReadOrigin block (fileSlot name) .owned
  | enclosing {name : String} : name ∉ block.owned → name ∈ block.enclosing →
      ReadOrigin block (fileSlot name) .enclosing
  | module {name : String} : name ∉ block.owned → name ∉ block.enclosing → name ∈ block.globals →
      ReadOrigin block (globalSlot name) .module

/-- The inner function body has a two-leaf mixed assignment followed
by a return. Each operand uses the existing bounded expression profile. -/
structure MixedBody where
  destination : String
  receiver : Operand
  index : Operand
  rhs : CompExpr
  returned : Operand

@[expose] def MixedBody.target (body : MixedBody) : Operand :=
  .tuple [.scalar (.read body.destination), .index body.receiver body.index]

@[expose] def MixedBody.statement (body : MixedBody) : Statement :=
  .seq (.assignTargetCompExpr body.target body.rhs) (.ret (some body.returned))

@[expose] def childBlock (parent : BlockContext) (parameters locals : List String) : LexicalBlock :=
  ⟨parameters ++ locals, parent.reads.locals, parent.reads.globals⟩

/-- Runtime body order for the bounded source fragment. RHS reads precede
target reads, which precede return reads. The declarative RHS rules
discard references bound by a comprehension's generator. -/
inductive BodyReads (block : LexicalBlock) : Statement → List Binding → Prop where
  | mixedReturn {name : String} {receiver index returned : Operand} {rhs : CompExpr}
      {pattern : Functions.Comprehensions.AssignmentPattern} {value : Functions.Comprehensions.Expression}
      {result : Functions.Lowering.Expr} {names : List String} {right target tail : List Binding} :
      RhsResolves block rhs value right →
      TargetResolves block .local (.tuple [.scalar (.read name), .index receiver index]) pattern names target →
      OperandResolves block returned result tail →
      BodyReads block
        (.seq (.assignTargetCompExpr (.tuple [.scalar (.read name), .index receiver index]) rhs)
          (.ret (some returned))) ((right ++ target) ++ tail)

/-- The exact compiled body paired with the independent mixed-assignment
and return witnesses in its lexical block. -/
inductive LeafCode (block : LexicalBlock) (body : MixedBody) : Functions.Body → Prop where
  | linked (assignment : ResolvedPatternAssignment) (returned : Functions.Lowering.Expr)
      (reads : List Binding) :
      AssignmentResolves block .local body.target body.rhs assignment →
      OperandResolves block body.returned returned reads →
      LeafCode block body
        (.seq (Functions.Comprehensions.assignPatternCode assignment.pattern assignment.rhs
          Functions.Comprehensions.directStages) (.returnExpr returned))

/-- Retain each free reference at its first occurrence. Module references
record the global slots actually read by the body. -/
inductive Selects (block : LexicalBlock) : List Binding → List FreeName → Prop where
  | nil : Selects block [] []
  | owned {first : Binding} {rest : List Binding} {free : List FreeName} :
      ReadOrigin block first .owned → Selects block (rest.filter fun later => !(later == first)) free →
      Selects block (first :: rest) free
  | enclosing {first : Binding} {rest : List Binding} {free : List FreeName} :
      ReadOrigin block first .enclosing → Selects block (rest.filter fun later => !(later == first)) free →
      Selects block (first :: rest) (⟨first, first⟩ :: free)
  | module {first : Binding} {rest : List Binding} {free : List FreeName} :
      ReadOrigin block first .module → Selects block (rest.filter fun later => !(later == first)) free →
      Selects block (first :: rest) (⟨first, first⟩ :: free)

/-- A resolved free reference receives an address from the defining frame.
A local may be owned by the immediate enclosing function or forwarded
through it. A module reference may also be passed through a function. -/
inductive ReceivesAddress (state : State) : FreeName → Lists.Capture → Prop where
  | enclosing {name : String} {address : Address} :
      state.slots (fileSlot name) = some (.owned address) →
      ReceivesAddress state ⟨fileSlot name, fileSlot name⟩ ⟨fileSlot name, address, true⟩
  | forwardedLocal {name : String} {address : Address} :
      state.slots (fileSlot name) = some (.captured address true) →
      ReceivesAddress state ⟨fileSlot name, fileSlot name⟩ ⟨fileSlot name, address, true⟩
  | ownedGlobal {name : String} {address : Address} :
      state.slots (globalSlot name) = some (.owned address) →
      ReceivesAddress state ⟨globalSlot name, globalSlot name⟩ ⟨globalSlot name, address, false⟩
  | capturedGlobal {name : String} {address : Address} :
      state.slots (globalSlot name) = some (.captured address false) →
      ReceivesAddress state ⟨globalSlot name, globalSlot name⟩ ⟨globalSlot name, address, false⟩

abbrev Installs (state : State) := InOrder (ReceivesAddress state)

end Silmaril.Languages.Starlark.Modules.Resolve.Capture
