module

public import Init

/-! # Python source syntax for module, function and class scope

This fragment starts at constructor data. Names have no resolved access
annotations. Function parameters are positional, with optional defaults
evaluated in the defining block.
-/

@[expose] public section
namespace Silmaril.Languages.Python.Source

abbrev Name := String

inductive BinaryOperator where
  | add | sub | mul
  deriving Repr

mutual
  inductive Expr where
    | name (identifier : Name)
    | integer (value : Int)
    | boolean (value : Bool)
    | none_
    | binary (operator : BinaryOperator) (left right : Expr)
    | call (callee : Expr) (arguments : List Expr)
    | attribute (receiver : Expr) (field : Name)
    | subscript (receiver index : Expr)
    | lambda (parameters : List Parameter) (body : Expr)
    deriving Repr

  structure Parameter where
    name : Name
    defaultValue : Option Expr := none
    deriving Repr
end

inductive Target where
  | name (identifier : Name)
  | attribute (receiver : Expr) (field : Name)
  | subscript (receiver index : Expr)
  | tuple (elements : List Target)
  | list_ (elements : List Target)
  deriving Repr

structure ImportName where
  member : Name
  alias : Option Name := none
  deriving Repr

mutual
  inductive Stmt where
    | assign (target : Name) (value : Expr)
    | assignTargets (targets : List Target) (value : Expr)
    | delete (target : Name)
    | deleteTargets (targets : List Target)
    | expression (value : Expr)
    | return_ (value : Option Expr)
    | raise_ (exception cause : Option Expr)
    | assert_ (condition : Expr) (message : Option Expr)
    | pass
    | break_
    | continue_
    | globalDecl (names : List Name)
    | nonlocalDecl (names : List Name)
    | if_ (condition : Expr) (body otherwise : List Stmt)
    | while_ (condition : Expr) (body otherwise : List Stmt)
    | for_ (target : Target) (iterator : Expr) (body otherwise : List Stmt)
    | try_ (body : List Stmt) (handlers : List ExceptHandler) (otherwise cleanup : List Stmt)
    | importFrom (modulePath : List Name) (level : Nat) (names : List ImportName)
    | functionDef (name : Name) (parameters : List Parameter) (body : List Stmt)
        (decorators : List Expr := [])
    | classDef (name : Name) (bases : List Expr) (body : List Stmt)
        (decorators : List Expr := [])
    deriving Repr

  structure ExceptHandler where
    condition : Option Expr
    target : Option Name
    body : List Stmt
    deriving Repr
end

structure Module where
  body : List Stmt
  deriving Repr

end Silmaril.Languages.Python.Source
