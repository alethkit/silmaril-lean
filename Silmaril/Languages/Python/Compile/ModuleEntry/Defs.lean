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

open Source (Access Comparison Expr Name Scope ScopeTree Stmt)

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

def scalarTuple? : Expr → Option (List Core.Module.Value)
  | .tuple elements => elements.mapM scalarLiteral?
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
      (operand : OperandTranslation scope expression test) (tail : Translation scope rest next) :
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
    let test ← lowerOperand scope condition
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
