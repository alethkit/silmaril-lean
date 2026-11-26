module

public import Silmaril.Languages.Starlark.Modules.Resolve.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Assignment

open Functions.Lowering.Resolve (Context)
open Functions.Comprehensions (AssignmentPattern Expression)

local notation "SourceOperand" => Functions.Lowering.Resolve.SourceExpr
local notation "ResolvedOperand" => Functions.Lowering.Expr

/-- The enclosing resolver supplies a collected block. An owned name shadows
an enclosing local, and both shadow module names. The runtime resolves an
enclosing local through the capture installed in the current frame. -/
structure LexicalBlock where
  owned : List String := []
  enclosing : List String := []
  globals : List String := []

@[expose] def LexicalBlock.context (block : LexicalBlock) : Context :=
  ⟨block.owned ++ block.enclosing, block.globals⟩

inductive ScalarName : String → Starlark.Value → Prop where
  | none : ScalarName "None" .none
  | true : ScalarName "True" (.bool true)
  | false : ScalarName "False" (.bool false)

/-- A lexical read gives its resolved expression and its contribution to
the source-order capture inputs. These rules do not run the resolver. -/
inductive ReadResolves (block : LexicalBlock) : String → ResolvedOperand → List Binding → Prop where
  | owned {name : String} : name ∈ block.owned →
      ReadResolves block name (.atom (.read (.bound ⟨.local, name⟩))) [⟨.local, name⟩]
  | enclosing {name : String} : name ∉ block.owned → name ∈ block.enclosing →
      ReadResolves block name (.atom (.read (.bound ⟨.local, name⟩))) [⟨.local, name⟩]
  | global {name : String} : name ∉ block.owned → name ∉ block.enclosing → name ∈ block.globals →
      ReadResolves block name (.atom (.read (.bound ⟨.global, name⟩))) [⟨.global, name⟩]
  | constant {name : String} {value : Starlark.Value} :
      name ∉ block.owned → name ∉ block.enclosing → name ∉ block.globals → ScalarName name value →
      ReadResolves block name (.atom (.read (.predeclared value))) []
  | builtin {name : String} {builtin : Lists.Builtin} :
      name ∉ block.owned → name ∉ block.enclosing → name ∉ block.globals → builtin.name = name →
      ReadResolves block name (.atom (.builtin builtin)) []

/-- The expression boundary of the independent assignment judgment. -/
inductive OperandInProfile : SourceOperand → Prop where
  | read (name : String) : OperandInProfile (.scalar (.read name))
  | int (value : Int) : OperandInProfile (.scalar (.int value))
  | string (value : String) : OperandInProfile (.string value)
  | index {receiver index : SourceOperand} : OperandInProfile receiver → OperandInProfile index →
      OperandInProfile (.index receiver index)
  | call {callee : SourceOperand} : OperandInProfile callee → OperandInProfile (.call callee [] [] none none)

inductive OperandResolves (block : LexicalBlock) : SourceOperand → ResolvedOperand → List Binding → Prop where
  | read {name : String} {value : ResolvedOperand} {reads : List Binding} :
      name.toList.head? ≠ some '$' → ReadResolves block name value reads →
      OperandResolves block (.scalar (.read name)) value reads
  | int (value : Int) : OperandResolves block (.scalar (.int value)) (.atom (.scalar (.int value))) []
  | string (text : String) : OperandResolves block (.string text) (.atom (.string text)) []
  | index {receiver index : SourceOperand} {recv sub : ResolvedOperand} {receiverReads indexReads : List Binding} :
      OperandResolves block receiver recv receiverReads → OperandResolves block index sub indexReads →
      OperandResolves block (.index receiver index) (.index recv sub) (receiverReads ++ indexReads)
  | call {callee : SourceOperand} {value : ResolvedOperand} {reads : List Binding} :
      OperandResolves block callee value reads →
      OperandResolves block (.call callee [] [] none none) (.call value [] [] none none) reads

inductive InOrder {α β : Type} (related : α → β → Prop) : List α → List β → Prop where
  | nil : InOrder related [] []
  | cons {first : α} {image : β} {rest : List α} {images : List β} :
      related first image → InOrder related rest images → InOrder related (first :: rest) (image :: images)

/-- Classify the left-hand side from its normalized syntax. The names are
exactly its identifier leaves, in order. Subscripts contribute no names. -/
inductive TargetShape (scope : Scope) :
    SourceOperand → AssignmentPattern SourceOperand × List String → Prop where
  | name (name : String) : TargetShape scope (.scalar (.read name)) (.name ⟨scope, name⟩, [name])
  | subscript (receiver index : SourceOperand) : TargetShape scope (.index receiver index) (.subscript receiver index, [])
  | list {children : List SourceOperand} {shapes : List (AssignmentPattern SourceOperand × List String)} :
      InOrder (TargetShape scope) children shapes →
      TargetShape scope (.list children) (.sequence (shapes.map Prod.fst), shapes.flatMap Prod.snd)
  | tuple {children : List SourceOperand} {shapes : List (AssignmentPattern SourceOperand × List String)} :
      InOrder (TargetShape scope) children shapes →
      TargetShape scope (.tuple children) (.sequence (shapes.map Prod.fst), shapes.flatMap Prod.snd)

inductive PatternInProfile : AssignmentPattern SourceOperand → Prop where
  | name (binding : Binding) : PatternInProfile (.name binding)
  | subscript {receiver index : SourceOperand} : OperandInProfile receiver → OperandInProfile index →
      PatternInProfile (.subscript receiver index)
  | sequence {children : List (AssignmentPattern SourceOperand)} :
      (∀ child ∈ children, PatternInProfile child) → PatternInProfile (.sequence children)

/-- Every shape of an admitted target uses only bounded store operands. -/
abbrev TargetInProfile (scope : Scope) (target : SourceOperand) : Prop :=
  ∀ shape names, TargetShape scope target (shape, names) → PatternInProfile shape

inductive PatternResolves (block : LexicalBlock) :
    AssignmentPattern SourceOperand → AssignmentPattern × List Binding → Prop where
  | name (binding : Binding) : PatternResolves block (.name binding) (.name binding, [])
  | subscript {receiver index : SourceOperand} {recv sub : ResolvedOperand} {receiverReads indexReads : List Binding} :
      OperandResolves block receiver recv receiverReads → OperandResolves block index sub indexReads →
      PatternResolves block (.subscript receiver index) (.subscript recv sub, receiverReads ++ indexReads)
  | sequence {children : List (AssignmentPattern SourceOperand)} {resolved : List (AssignmentPattern × List Binding)} :
      InOrder (PatternResolves block) children resolved →
      PatternResolves block (.sequence children) (.sequence (resolved.map Prod.fst), resolved.flatMap Prod.snd)

@[expose] def TargetResolves (block : LexicalBlock) (scope : Scope) (target : SourceOperand) (pattern : AssignmentPattern)
    (names : List String) (reads : List Binding) : Prop :=
  ∃ shape, TargetShape scope target (shape, names) ∧ PatternResolves block shape (pattern, reads)

inductive RhsInProfile : CompExpr → Prop where
  | plain {source : SourceOperand} : OperandInProfile source → RhsInProfile (.plain source)
  | list {name : String} {iterable element : SourceOperand} :
      OperandInProfile iterable → OperandInProfile element →
      RhsInProfile (.list ⟨.scalar (.read name), iterable, .yield element⟩)

/-- Independent RHS witnesses for the bounded composition. A single
generator's iterable uses the enclosing block and its yield uses the
fresh local binding. Captures exclude reads of that fresh local. -/
inductive RhsResolves (block : LexicalBlock) : CompExpr → Expression → List Binding → Prop where
  | plain {source : SourceOperand} {value : ResolvedOperand} {reads : List Binding} :
      OperandResolves block source value reads → RhsResolves block (.plain source) (.plain value) reads
  | list {name : String} {iterable element : SourceOperand} {iterated emitted : ResolvedOperand}
      {outer inner : List Binding} :
      OperandResolves block iterable iterated outer →
      OperandResolves { block with owned := name :: block.owned } element emitted inner →
      RhsResolves block (.list ⟨.scalar (.read name), iterable, .yield element⟩)
        (.list ⟨[fileSlot name], .name (fileSlot name), iterated, .yield emitted⟩)
        (outer ++ inner.filter (fun read => !(fileSlot name == read)))

structure AssignmentResolves (block : LexicalBlock) (scope : Scope) (target : SourceOperand)
    (rhs : CompExpr) (result : ResolvedPatternAssignment) : Prop where
  targetResolves : TargetResolves block scope target result.pattern result.names result.targetReads
  rhsResolves : RhsResolves block rhs result.rhs result.rhsReads

end Silmaril.Languages.Starlark.Modules.Resolve.Assignment
