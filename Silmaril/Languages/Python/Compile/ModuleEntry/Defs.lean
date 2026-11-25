module

public import Silmaril.Languages.Python.Source.Scope.Defs
public import Silmaril.Languages.Python.Core.Module.Defs

/-! # Check Python module-entry syntax and global name bindings

This source profile keeps name keys for global reads and writes and
retains message-free assertions in execution order. Each reference records
the analyzed access. The plan is independent of a runtime store.
-/

@[expose] public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry

open Source (Access BooleanOperator Comparison Expr Name Scope ScopeTree Stmt)

structure GlobalReference (scope : Scope) (name : Name) where
  access : Access
  resolved : scope.access name = some access
  globalAccess : access = .moduleName ∨ access = .declaredGlobal

def globalReference? (scope : Scope) (name : Name) : Option (GlobalReference scope name) :=
  if moduleName : scope.access name = some .moduleName then
    some ⟨.moduleName, moduleName, Or.inl rfl⟩
  else if declared : scope.access name = some .declaredGlobal then
    some ⟨.declaredGlobal, declared, Or.inr rfl⟩
  else none

inductive BinaryOp where
  | add | floorDiv | equal

inductive Operand (scope : Scope) where
  | integer (value : Int)
  | boolean (value : Bool)
  | read (name : Name) (reference : GlobalReference scope name)
  | binary (op : BinaryOp) (left right : Operand scope)

def integerLiteral? : Expr → Option Int
  | .integer value => some value
  | .unary .negative (.integer value) => some (-value)
  | _ => none

def literalGuard? : Expr → Option Bool
  | .boolean value => some value
  | expression => (integerLiteral? expression).map fun value => value != 0

def literalSequence? : Expr → Option (List Int)
  | .list_ elements | .tuple elements => elements.mapM integerLiteral?
  | _ => none

/-- A negative index counts once from the end of the literal sequence. -/
def literalIndex? (values : List Int) (index : Int) : Option Int :=
  let offset := if index < 0 then (values.length : Int) + index else index
  if offset < 0 then none else values[offset.toNat]?

def literalSubscript? (source index : Expr) : Option Int := do
  let values ← literalSequence? source
  let position ← integerLiteral? index
  literalIndex? values position

def scalarLiteral? : Expr → Option Core.Module.Value
  | .boolean value => some (.bool value)
  | expression => (integerLiteral? expression).map .int

inductive ScalarComparison where
  | eq | ne | lt | le | gt | ge

def ScalarComparison.ofSource? : Comparison → Option ScalarComparison
  | .eq => some .eq
  | .ne => some .ne
  | .lt => some .lt
  | .le => some .le
  | .gt => some .gt
  | .ge => some .ge
  | _ => none

/-- Only exact integers and Booleans enter this numeric comparison. -/
def ScalarComparison.test (operator : ScalarComparison) (left right : Core.Module.Value) : Bool :=
  match operator with
  | .eq => left.equal right
  | .ne => !left.equal right
  | .lt => decide (left.asInt < right.asInt)
  | .le => decide (left.asInt ≤ right.asInt)
  | .gt => decide (left.asInt > right.asInt)
  | .ge => decide (left.asInt ≥ right.asInt)

/-- Each reached right value also supplies the next comparison's left value.
A false link stops the comparison scan. -/
def ScalarComparison.chain (left : Core.Module.Value) : List (ScalarComparison × Core.Module.Value) → Bool
  | [] => true
  | (operator, right) :: rest =>
    if operator.test left right then chain right rest else false

inductive ScalarComparison.EvaluatesChain :
    Core.Module.Value → List (ScalarComparison × Core.Module.Value) → Bool → Prop where
  | done (left : Core.Module.Value) : EvaluatesChain left [] true
  | stop {left operator right rest} (failed : operator.test left right = false) :
      EvaluatesChain left ((operator, right) :: rest) false
  | next {left operator right rest result} (passed : operator.test left right = true)
      (tail : EvaluatesChain right rest result) : EvaluatesChain left ((operator, right) :: rest) result

def literalComparisonLink? (link : Comparison × Expr) : Option (ScalarComparison × Core.Module.Value) := do
  let operator ← ScalarComparison.ofSource? link.1
  let value ← scalarLiteral? link.2
  return (operator, value)

/-- Validate the whole chain before scanning for the first false comparison. -/
def literalComparisonChain? (left : Expr) (links : List (Comparison × Expr)) : Option Bool :=
  match links with
  | _ :: _ :: _ => do
    let value ← scalarLiteral? left
    let checked ← links.mapM literalComparisonLink?
    return ScalarComparison.chain value checked
  | _ => none

def scalarTuple? : Expr → Option (List Core.Module.Value)
  | .tuple elements => elements.mapM scalarLiteral?
  | _ => none

/-- These literals can be used for truth tests without representing a container
or `None` as a scalar runtime value. Every element must pass the literal check. -/
def nonScalarLiteralTruth? : Expr → Option Bool
  | .none_ => some false
  | .tuple elements | .list_ elements => do
    let values ← elements.mapM scalarLiteral?
    return !values.isEmpty
  | _ => none

def literalNegation? (source : Expr) : Option Bool :=
  match scalarLiteral? source with
  | some value => some (!value.truth)
  | none => (nonScalarLiteralTruth? source).map (! ·)

def continuesSelection (operator : BooleanOperator) (value : Core.Module.Value) : Bool :=
  match operator with
  | .and_ => value.truth
  | .or_ => !value.truth

/-- A connective returns an operand value, with its original type. -/
def selectScalar (operator : BooleanOperator) (value : Core.Module.Value) :
    List Core.Module.Value → Core.Module.Value
  | [] => value
  | next :: rest =>
    if continuesSelection operator value then selectScalar operator next rest else value

inductive SelectsScalar (operator : BooleanOperator) :
    Core.Module.Value → List Core.Module.Value → Core.Module.Value → Prop where
  | last (value : Core.Module.Value) : SelectsScalar operator value [] value
  | stop {value next rest} (stopped : continuesSelection operator value = false) :
      SelectsScalar operator value (next :: rest) value
  | next {value next rest result} (continued : continuesSelection operator value = true)
      (tail : SelectsScalar operator next rest result) :
      SelectsScalar operator value (next :: rest) result

def literalBooleanOp? (operator : BooleanOperator) : List Expr → Option Core.Module.Value
  | first :: second :: rest => do
    let value ← scalarLiteral? first
    let values ← (second :: rest).mapM scalarLiteral?
    return selectScalar operator value values
  | _ => none

def literalTupleMember? (left right : Expr) : Option Bool := do
  let needle ← scalarLiteral? left
  let elements ← scalarTuple? right
  return elements.any (needle.equal ·)

/-- Read only closed literal operands. Tuple equality compares corresponding
elements and lengths. Membership tests scalar equality in tuple order. -/
def literalTupleComparison? (left : Expr) (operator : Comparison) (right : Expr) : Option Bool :=
  match operator with
  | .eq => do
    let lhs ← scalarTuple? left
    let rhs ← scalarTuple? right
    return lhs.isEqv rhs Core.Module.Value.equal
  | .in_ => literalTupleMember? left right
  | .notIn => (literalTupleMember? left right).map (! ·)
  | _ => none

/-- Deliver a computed Boolean through the existing typed scalar equality. -/
def Operand.booleanResult {scope : Scope} (value : Bool) : Operand scope :=
  .binary .equal (.boolean value) (.boolean true)

def Operand.scalarResult {scope : Scope} : Core.Module.Value → Operand scope
  | .int value => .integer value
  | .bool value => .booleanResult value

def Operand.conditionalResult {scope : Scope} : Operand scope → Operand scope
  | .boolean value => .booleanResult value
  | value => value

inductive OperandTranslation (scope : Scope) : Expr → Operand scope → Prop where
  | integer (value : Int) : OperandTranslation scope (.integer value) (.integer value)
  | boolean (value : Bool) : OperandTranslation scope (.boolean value) (.boolean value)
  | negativeInteger (value : Int) :
      OperandTranslation scope (.unary .negative (.integer value)) (.integer (-value))
  | literalSubscript {source index value} (selected : literalSubscript? source index = some value) :
      OperandTranslation scope (.subscript source index) (.integer value)
  | read (name : Name) (reference : GlobalReference scope name) :
      OperandTranslation scope (.name name) (.read name reference)
  | add {left right lhs rhs} (first : OperandTranslation scope left lhs)
      (second : OperandTranslation scope right rhs) :
      OperandTranslation scope (.binary .add left right) (.binary .add lhs rhs)
  | floorDiv {left right lhs rhs} (first : OperandTranslation scope left lhs)
      (second : OperandTranslation scope right rhs) :
      OperandTranslation scope (.binary .floorDiv left right) (.binary .floorDiv lhs rhs)
  | equal {left right lhs rhs} (first : OperandTranslation scope left lhs)
      (second : OperandTranslation scope right rhs) :
      OperandTranslation scope (.comparison left [(.eq, right)]) (.binary .equal lhs rhs)
  | literalTupleComparison {left operator right value}
      (checked : literalTupleComparison? left operator right = some value) :
      OperandTranslation scope (.comparison left [(operator, right)]) (.booleanResult value)
  | literalComparisonChain {left first second rest value}
      (checked : literalComparisonChain? left (first :: second :: rest) = some value) :
      OperandTranslation scope (.comparison left (first :: second :: rest)) (.booleanResult value)
  | literalNegation {source value} (checked : literalNegation? source = some value) :
      OperandTranslation scope (.unary .not_ source) (.booleanResult value)
  | literalBooleanOp {operator operands value} (checked : literalBooleanOp? operator operands = some value) :
      OperandTranslation scope (.booleanOp operator operands) (.scalarResult value)
  | literalConditional {condition yes no decision lhs rhs}
      (guard : literalGuard? condition = some decision)
      (positive : OperandTranslation scope yes lhs) (negative : OperandTranslation scope no rhs) :
      OperandTranslation scope (.conditional condition yes no)
        (if decision then lhs else rhs).conditionalResult

inductive Action (scope : Scope) where
  | assign (name : Name) (reference : GlobalReference scope name) (value : Operand scope)
  | assertion (condition : Operand scope)

inductive Error where
  | scope (diagnostic : Source.Diagnostic)
  | moduleScope
  | unresolvedGlobal (name : Name)
  | expressionProfile
  | assertionMessage
  | statementProfile
  deriving BEq, DecidableEq, Repr

def lowerOperand (scope : Scope) : (source : Expr) → Except Error {value // OperandTranslation scope source value}
  | .integer value => .ok ⟨.integer value, .integer value⟩
  | .boolean value => .ok ⟨.boolean value, .boolean value⟩
  | .unary .negative (.integer value) => .ok ⟨.integer (-value), .negativeInteger value⟩
  | .unary .not_ operand =>
    match folded : literalNegation? operand with
    | some value => .ok ⟨.booleanResult value, .literalNegation folded⟩
    | none => .error .expressionProfile
  | .booleanOp operator operands =>
    match folded : literalBooleanOp? operator operands with
    | some value => .ok ⟨.scalarResult value, .literalBooleanOp folded⟩
    | none => .error .expressionProfile
  | .subscript source index =>
    match selected : literalSubscript? source index with
    | some value => .ok ⟨.integer value, .literalSubscript selected⟩
    | none => .error .expressionProfile
  | .name name => do
    let some reference := globalReference? scope name | throw (.unresolvedGlobal name)
    return ⟨.read name reference, .read name reference⟩
  | .binary .add left right => do
    let lhs ← lowerOperand scope left
    let rhs ← lowerOperand scope right
    return ⟨.binary .add lhs.val rhs.val, .add lhs.property rhs.property⟩
  | .binary .floorDiv left right => do
    let lhs ← lowerOperand scope left
    let rhs ← lowerOperand scope right
    return ⟨.binary .floorDiv lhs.val rhs.val, .floorDiv lhs.property rhs.property⟩
  | .comparison left [(operator, right)] =>
    match folded : literalTupleComparison? left operator right with
    | some value => .ok ⟨.booleanResult value, .literalTupleComparison folded⟩
    | none =>
      match operator with
      | .eq => do
        let lhs ← lowerOperand scope left
        let rhs ← lowerOperand scope right
        return ⟨.binary .equal lhs.val rhs.val, .equal lhs.property rhs.property⟩
      | _ => .error .expressionProfile
  | .comparison left (first :: second :: rest) =>
    match folded : literalComparisonChain? left (first :: second :: rest) with
    | some value => .ok ⟨.booleanResult value, .literalComparisonChain folded⟩
    | none => .error .expressionProfile
  | .conditional condition yes no =>
    match guard : literalGuard? condition with
    | none => .error .expressionProfile
    | some decision => do
      let positive ← lowerOperand scope yes
      let negative ← lowerOperand scope no
      return ⟨(if decision then positive.val else negative.val).conditionalResult,
        .literalConditional guard positive.property negative.property⟩
  | _ => .error .expressionProfile
termination_by source => sizeOf source

inductive TestTranslation (scope : Scope) : Expr → Operand scope → Prop where
  | operand {source value} (translated : OperandTranslation scope source value) :
      TestTranslation scope source value
  | literalTruth {source value} (checked : nonScalarLiteralTruth? source = some value) :
      TestTranslation scope source (.booleanResult value)

def lowerTest (scope : Scope) (source : Expr) : Except Error {value // TestTranslation scope source value} :=
  match checked : nonScalarLiteralTruth? source with
  | some value => .ok ⟨.booleanResult value, .literalTruth checked⟩
  | none => (lowerOperand scope source).map fun operand => ⟨operand.val, .operand operand.property⟩

inductive Binding : Stmt → Name → Expr → Prop where
  | direct (name : Name) (value : Expr) : Binding (.assign name value) name value
  | singleton (name : Name) (value : Expr) : Binding (.assignTargets [.name name] value) name value

def binding? : (statement : Stmt) → Option {pair : Name × Expr // Binding statement pair.1 pair.2}
  | .assign name value => some ⟨(name, value), .direct name value⟩
  | .assignTargets [.name name] value => some ⟨(name, value), .singleton name value⟩
  | _ => none

/-- Arm statements neither introduce child scopes nor install directives.
The operand checker also checks expressions in both arms. -/
def literalArmStatement : Stmt → Bool
  | .assert_ _ none | .pass => true
  | statement => (binding? statement).isSome

/-- A literal Boolean assertion uses only truth. Emit the equivalent
integer test so this arm uses the same assertion path in both runners. -/
def Action.inLiteralArm {scope : Scope} : Action scope → Action scope
  | .assertion (.boolean value) => .assertion (.integer (if value then 1 else 0))
  | action => action

inductive Translation (scope : Scope) : List Stmt → List (Action scope) → Prop where
  | done : Translation scope [] []
  | assign {statement name expression reference value rest next}
      (binding : Binding statement name expression)
      (operand : OperandTranslation scope expression value) (tail : Translation scope rest next) :
      Translation scope (statement :: rest) (.assign name reference value :: next)
  | assertion {expression test rest next}
      (operand : TestTranslation scope expression test) (tail : Translation scope rest next) :
      Translation scope (.assert_ expression none :: rest) (.assertion test :: next)
  | globals {names rest next} (tail : Translation scope rest next) :
      Translation scope (.globalDecl names :: rest) next
  | pass {rest next} (tail : Translation scope rest next) :
      Translation scope (.pass :: rest) next
  | literalIf {condition yes no rest decision positive negative next}
      (arms : (yes.all literalArmStatement && no.all literalArmStatement) = true)
      (guard : literalGuard? condition = some decision)
      (yesTranslation : Translation scope yes positive) (noTranslation : Translation scope no negative)
      (tail : Translation scope rest next) :
      Translation scope (.if_ condition yes no :: rest)
        ((if decision then positive else negative).map Action.inLiteralArm ++ next)

def lowerStatements (scope : Scope) : (body : List Stmt) →
    Except Error {actions // Translation scope body actions}
  | [] => .ok ⟨[], .done⟩
  | .assert_ condition none :: body => do
    let test ← lowerTest scope condition
    let tail ← lowerStatements scope body
    return ⟨.assertion test.val :: tail.val, .assertion test.property tail.property⟩
  | .assert_ _ (some _) :: _ => .error .assertionMessage
  | .globalDecl _ :: body => do
    let tail ← lowerStatements scope body
    return ⟨tail.val, .globals tail.property⟩
  | .pass :: body => do
    let tail ← lowerStatements scope body
    return ⟨tail.val, .pass tail.property⟩
  | .if_ condition yes no :: body => do
    if arms : (yes.all literalArmStatement && no.all literalArmStatement) = true then
      match guard : literalGuard? condition with
      | none => throw .statementProfile
      | some decision =>
        let positive ← lowerStatements scope yes
        let negative ← lowerStatements scope no
        let tail ← lowerStatements scope body
        return ⟨(if decision then positive.val else negative.val).map Action.inLiteralArm ++ tail.val,
          .literalIf arms guard positive.property negative.property tail.property⟩
    else throw .statementProfile
  | statement :: body => do
    let some ⟨(name, expression), binding⟩ := binding? statement | throw .statementProfile
    let some reference := globalReference? scope name | throw (.unresolvedGlobal name)
    let value ← lowerOperand scope expression
    let tail ← lowerStatements scope body
    return ⟨.assign name reference value.val :: tail.val, .assign binding value.property tail.property⟩
termination_by body => sizeOf body

structure Checked (source : Source.Module) where
  tree : ScopeTree
  analyzed : Source.analyze source = .ok tree
  moduleScope : tree.scope.context.kind = .module_
  actions : List (Action tree.scope)
  lowered : Translation tree.scope source.body actions

def check (source : Source.Module) : Except Error (Checked source) :=
  match analyzed : Source.analyze source with
  | .error diagnostic => .error (.scope diagnostic)
  | .ok tree =>
    if kind : tree.scope.context.kind = .module_ then
      (lowerStatements tree.scope source.body).map fun lowering =>
        ⟨tree, analyzed, kind, lowering.val, lowering.property⟩
    else .error .moduleScope

end Silmaril.Languages.Python.Compile.ModuleEntry
