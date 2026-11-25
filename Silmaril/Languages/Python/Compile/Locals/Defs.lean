module

public import Silmaril.Languages.Python.Core.Locals.Defs
public import Silmaril.Languages.Python.Source.Scope.Defs

/-! # Lowering one Python integer-local frame

The module contains one undecorated, parameterless function. Its core
artifact consists of scalar local assignments followed by a return.
Names are accepted only with the analyzed block's local access and a
matching slot witness.
-/

@[expose] public section
namespace Silmaril.Languages.Python.Compile.Locals

abbrev Frame := Core.Locals.Code

def localNames (scope : Source.Scope) : List Source.Name :=
  scope.context.assigned.reverse.filter (fun name => decide (scope.access name = some .local))

structure Address (scope : Source.Scope) (name : Source.Name) where
  index : Fin (localNames scope).length
  lookup_eq : (localNames scope)[index] = name
  access_eq : scope.access name = some .local

inductive Error where
  | scope (diagnostic : Source.Diagnostic)
  | moduleShape
  | missingFunctionScope
  | bodyShape
  | expressionShape
  | unresolvedLocal (name : Source.Name)
  deriving BEq, DecidableEq, Repr

def address? (scope : Source.Scope) (name : Source.Name) : Option (Address scope name) :=
  if access : scope.access name = some .local then
    let selected := (localNames scope).findFinIdx? (fun candidate => decide (candidate = name))
    selected.pmap (p := fun index => selected = some index)
      (fun index found => ⟨index, of_decide_eq_true (List.findFinIdx?_eq_some_iff.mp found).1, access⟩)
      (fun _ found => Option.mem_def.mp found)
  else none

inductive OperatorTranslation : Source.BinaryOperator → Core.BinOp → Prop where
  | add : OperatorTranslation .add .add
  | floorDiv : OperatorTranslation .floorDiv .floorDiv

def operator? : (op : Source.BinaryOperator) → Option {target // OperatorTranslation op target}
  | .add => some ⟨.add, .add⟩
  | .floorDiv => some ⟨.floorDiv, .floorDiv⟩
  | _ => none

inductive RhsTranslation (scope : Source.Scope) :
    Source.Expr → Core.Locals.Rhs (localNames scope).length → Prop where
  | integer (value : Int) : RhsTranslation scope (.integer value) (.arithmetic (.int value))
  | name (name : Source.Name) (address : Address scope name) :
      RhsTranslation scope (.name name) (.read address.index)
  | binary {op : Source.BinaryOperator} {targetOp : Core.BinOp}
      {left right : Source.Expr} {lhs rhs : Core.Locals.Rhs (localNames scope).length}
      (operator : OperatorTranslation op targetOp)
      (leftTranslation : RhsTranslation scope left lhs)
      (rightTranslation : RhsTranslation scope right rhs) :
      RhsTranslation scope (.binary op left right) (.binary targetOp lhs rhs)

def lowerRhs (scope : Source.Scope) : (source : Source.Expr) →
    Except Error {target // RhsTranslation scope source target}
  | .integer value => .ok ⟨.arithmetic (.int value), .integer value⟩
  | .name name =>
    match address? scope name with
    | none => .error (.unresolvedLocal name)
    | some address => .ok ⟨.read address.index, .name name address⟩
  | .binary op left right =>
    match operator? op with
    | none => .error .expressionShape
    | some ⟨targetOp, operator⟩ => do
      let lhs ← lowerRhs scope left
      let rhs ← lowerRhs scope right
      return ⟨.binary targetOp lhs.val rhs.val, .binary operator lhs.property rhs.property⟩
  | _ => .error .expressionShape

inductive Assignment : Source.Stmt → Source.Name → Source.Expr → Prop where
  | scalar (name : Source.Name) (value : Source.Expr) : Assignment (.assign name value) name value
  | singleTarget (name : Source.Name) (value : Source.Expr) :
      Assignment (.assignTargets [.name name] value) name value

def assignment? : (statement : Source.Stmt) →
    Option {pair : Source.Name × Source.Expr // Assignment statement pair.1 pair.2}
  | .assign name value => some ⟨(name, value), .scalar name value⟩
  | .assignTargets [.name name] value => some ⟨(name, value), .singleTarget name value⟩
  | _ => none

inductive BodyTranslation (scope : Source.Scope) :
    List Source.Stmt → Frame (localNames scope).length → Prop where
  | ret {value : Source.Expr} {rhs : Core.Locals.Rhs (localNames scope).length}
      (translated : RhsTranslation scope value rhs) :
      BodyTranslation scope [.return_ (some value)] (.ret rhs)
  | assign {statement : Source.Stmt} {name : Source.Name} {value : Source.Expr}
      {rest : List Source.Stmt} {rhs : Core.Locals.Rhs (localNames scope).length}
      {next : Frame (localNames scope).length}
      (assignment : Assignment statement name value) (address : Address scope name)
      (translated : RhsTranslation scope value rhs) (remaining : BodyTranslation scope rest next) :
      BodyTranslation scope (statement :: rest) (.assign address.index rhs next)

def lowerBody (scope : Source.Scope) : (body : List Source.Stmt) →
    Except Error {code // BodyTranslation scope body code}
  | [.return_ (some value)] => do
    let rhs ← lowerRhs scope value
    return ⟨.ret rhs.val, .ret rhs.property⟩
  | statement :: rest =>
    match assignment? statement with
    | none => .error .bodyShape
    | some ⟨(name, value), assignment⟩ =>
      match address? scope name with
      | none => .error (.unresolvedLocal name)
      | some address => do
        let rhs ← lowerRhs scope value
        let tail ← lowerBody scope rest
        return ⟨.assign address.index rhs.val tail.val,
          .assign assignment address rhs.property tail.property⟩
  | [] => .error .bodyShape

structure Compiled (source : Source.Module) where
  name : Source.Name
  body : List Source.Stmt
  shape : source = ⟨[.functionDef name [] body [] none]⟩
  tree : Source.ScopeTree
  analyzed : Source.analyze source = .ok tree
  scope : Source.Scope
  located : tree.atPath [0] = some scope
  code : Frame (localNames scope).length
  translated : BodyTranslation scope body code

def compile (source : Source.Module) : Except Error (Compiled source) :=
  match analyzed : Source.analyze source with
  | .error diagnostic => .error (.scope diagnostic)
  | .ok tree =>
    match shape : source with
    | ⟨[.functionDef name [] body [] none]⟩ =>
      match located : tree.atPath [0] with
      | none => .error .missingFunctionScope
      | some scope =>
        (lowerBody scope body).map fun lowered =>
          ⟨name, body, rfl, tree, shape ▸ analyzed, scope, located, lowered.val, lowered.property⟩
    | _ => .error .moduleShape

end Silmaril.Languages.Python.Compile.Locals
