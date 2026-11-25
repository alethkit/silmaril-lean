module

public import Silmaril.Courses.Cambridge.L3.Syntax

/-! # Named L3 syntax and scope resolution (Sewell §5.5, p. 78) -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3

inductive RawExpr where
  | int (value : Int)
  | bool (value : Bool)
  | binary (left : RawExpr) (op : Op) (right : RawExpr)
  | cond (test yes no : RawExpr)
  | assign (lhs rhs : RawExpr)
  | deref (reference : RawExpr)
  | ref (value : RawExpr)
  | loc (address : Loc)
  | skip
  | seq (left right : RawExpr)
  | loop (test body : RawExpr)
  | var (name : Var)
  | lam (name : Var) (domain : Ty) (body : RawExpr)
  | app (function argument : RawExpr)
  | letE (name : Var) (type : Ty) (value body : RawExpr)
  | letRecFun (function parameter : Var) (domain codomain : Ty) (functionBody body : RawExpr)
  | pair (left right : RawExpr)
  | fst (pair : RawExpr)
  | snd (pair : RawExpr)
  | inl (payload : RawExpr) (sumType : Ty)
  | inr (payload : RawExpr) (sumType : Ty)
  | matchSum (scrutinee : RawExpr) (leftName : Var) (leftType : Ty) (left : RawExpr)
      (rightName : Var) (rightType : Ty) (right : RawExpr)
  | record (labels : RecordLabels) (fields : labels.Index → RawExpr)
  | project (record : RawExpr) (label : Label)

/-- The nearest binder comes first. Names absent from the list remain free. -/
def RawExpr.resolve (bound : List Var) : RawExpr → Expr
  | .int n => .int n
  | .bool b => .bool b
  | .binary left op right => .binary (left.resolve bound) op (right.resolve bound)
  | .cond test yes no => .cond (test.resolve bound) (yes.resolve bound) (no.resolve bound)
  | .assign lhs rhs => .assign (lhs.resolve bound) (rhs.resolve bound)
  | .deref e => .deref (e.resolve bound)
  | .ref e => .ref (e.resolve bound)
  | .loc address => .loc address
  | .skip => .skip
  | .seq left right => .seq (left.resolve bound) (right.resolve bound)
  | .loop test body => .loop (test.resolve bound) (body.resolve bound)
  | .var name =>
      match bound.idxOf? name with
      | some i => .bvar i
      | none => .fvar name
  | .lam name domain body => .lam domain (body.resolve (name :: bound))
  | .app fn arg => .app (fn.resolve bound) (arg.resolve bound)
  | .letE name type value body =>
      .letE type (value.resolve bound) (body.resolve (name :: bound))
  | .letRecFun fn param domain codomain fnBody body =>
      .letRecFun domain codomain (fnBody.resolve (param :: fn :: bound)) (body.resolve (fn :: bound))
  | .pair left right => .pair (left.resolve bound) (right.resolve bound)
  | .fst e => .fst (e.resolve bound)
  | .snd e => .snd (e.resolve bound)
  | .inl e T => .inl (e.resolve bound) T
  | .inr e T => .inr (e.resolve bound) T
  | .matchSum e x A left y B right =>
      .matchSum (e.resolve bound) A (left.resolve (x :: bound)) B (right.resolve (y :: bound))
  | .record labels fields => .record labels (fun i => (fields i).resolve bound)
  | .project e label => .project (e.resolve bound) label

end Silmaril.Courses.Cambridge.L3
