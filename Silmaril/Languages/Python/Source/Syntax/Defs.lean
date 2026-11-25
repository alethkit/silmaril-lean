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
    | lambda (parameters : List Parameter) (body : Expr)
    deriving Repr

  structure Parameter where
    name : Name
    defaultValue : Option Expr := none
    deriving Repr
end

inductive Stmt where
  | assign (target : Name) (value : Expr)
  | delete (target : Name)
  | expression (value : Expr)
  | return_ (value : Option Expr)
  | pass
  | globalDecl (names : List Name)
  | nonlocalDecl (names : List Name)
  | if_ (condition : Expr) (body otherwise : List Stmt)
  | while_ (condition : Expr) (body otherwise : List Stmt)
  | functionDef (name : Name) (parameters : List Parameter) (body : List Stmt)
      (decorators : List Expr := [])
  | classDef (name : Name) (bases : List Expr) (body : List Stmt)
      (decorators : List Expr := [])
  deriving Repr

structure Module where
  body : List Stmt
  deriving Repr

end Silmaril.Languages.Python.Source
