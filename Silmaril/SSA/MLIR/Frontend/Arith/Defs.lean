module

public import Silmaril.SSA.MLIR.Arith.Defs

/-! # Admission for decoded scalar arithmetic

Check names, widths, and isolated scopes before constructing an intrinsic
arithmetic block. Unsupported decoded forms fail admission.
-/

@[expose] public section

namespace Silmaril.MLIR.Frontend.Arith

open Silmaril.MLIR.Arith (Block Rhs Var Width)

structure Decl where
  name : String
  width : Nat

inductive Expr where
  | constant (value : Int)
  | binary (op : Silmaril.MLIR.Arith.BinOp) (lhs rhs : String)

inductive Terminator where
  | ret
  | yield
  deriving DecidableEq, Repr

/-- Decoded operation spine. The decoder can mark out-of-profile syntax explicitly. -/
inductive Code where
  | finish (kind : Terminator) (operand : String) (width : Nat)
  | letOp (result : Decl) (rhs : Expr) (rest : Code)
  | letRegion (result : Decl) (operand : String) (parameter : Decl) (body rest : Code)
  | unsupported (form : String)

structure Program where
  inputs : List Decl
  resultWidth : Nat
  body : Code

inductive Diagnostic where
  | unknownReference (name : String)
  | duplicateName (name : String)
  | widthMismatch (name : String) (expected actual : Nat)
  | zeroWidth (binding : Option String)
  | illegalCapture (name : String)
  | wrongTerminator (expected actual : Terminator)
  | unsupported (form : String)
  deriving DecidableEq, Repr

abbrev Scope := List (String × Width)

/-- Successful lookup certifies the name and width at the emitted de Bruijn index. -/
structure Resolved (scope : Scope) (name : String) (w : Width) where
  var : Var (scope.map Prod.snd) w
  atIndex : scope[var.index]? = some (name, w)

/-- Search the local scope in index order. `outer` supplies names for capture
errors and never contributes a reference. -/
def resolve (outer : List String) (name : String) (w : Width) :
    (scope : Scope) → Except Diagnostic (Resolved scope name w)
  | [] =>
      if outer.contains name then .error (.illegalCapture name)
      else .error (.unknownReference name)
  | (localName, actual) :: scope =>
      if sameName : localName = name then
        if sameWidth : actual = w then by
          subst localName
          subst actual
          exact .ok ⟨.here, rfl⟩
        else .error (.widthMismatch name w.val actual.val)
      else do
        let found ← resolve outer name w scope
        return ⟨.there found.var, by simpa [Var.index] using found.atIndex⟩

/-- The checked signature and intrinsic block. The input scope retains the
source input order, with the first input at index zero. -/
structure Admitted where
  scope : Scope
  resultWidth : Width
  block : Block (scope.map Prod.snd) resultWidth

/-- Check a decoded program. Each operation adds its result only for the rest
of the block. Each region starts with a fresh scope holding only its parameter. -/
def Program.elaborate (program : Program) : Except Diagnostic Admitted := do
  let scope ← checkInputs [] program.inputs
  let w ← checkWidth none program.resultWidth
  let block ← elaborateCode w .ret [] scope program.body
  return ⟨scope, w, block⟩
where
  checkWidth (binding : Option String) (w : Nat) : Except Diagnostic Width :=
    if positive : 0 < w then .ok ⟨w, positive⟩ else .error (.zeroWidth binding)

  checkDecl (scope : Scope) (decl : Decl) : Except Diagnostic Width := do
    if (scope.lookup decl.name).isSome then throw (.duplicateName decl.name)
    checkWidth (some decl.name) decl.width

  checkInputs (scope : Scope) : List Decl → Except Diagnostic Scope
    | [] => pure scope.reverse
    | input :: inputs => do
        let w ← checkDecl scope input
        checkInputs ((input.name, w) :: scope) inputs

  elaborateExpr (outer : List String) (scope : Scope) (w : Width) :
      Expr → Except Diagnostic (Rhs (scope.map Prod.snd) w)
    | .constant value => pure (.constant (BitVec.ofInt w.val value))
    | .binary op lhs rhs => do
        let lhs ← resolve outer lhs w scope
        let rhs ← resolve outer rhs w scope
        return .binary op lhs.var rhs.var

  elaborateCode (resultWidth : Width) (terminator : Terminator)
      (outer : List String) (scope : Scope) :
      Code → Except Diagnostic (Block (scope.map Prod.snd) resultWidth)
    | .finish kind operand width => do
        if kind != terminator then throw (.wrongTerminator terminator kind)
        if width != resultWidth.val then throw (.widthMismatch operand resultWidth.val width)
        let result ← resolve outer operand resultWidth scope
        return .yield result.var
    | .letOp result rhs rest => do
        let w ← checkDecl scope result
        let rhs ← elaborateExpr outer scope w rhs
        let rest ← elaborateCode resultWidth terminator outer ((result.name, w) :: scope) rest
        return .letOp rhs rest
    | .letRegion result operand parameter body rest => do
        let w ← checkDecl scope result
        let parameterWidth ← checkWidth (some parameter.name) parameter.width
        let arg ← resolve outer operand parameterWidth scope
        let body ← elaborateCode w .yield (scope.map Prod.fst ++ outer)
          [(parameter.name, parameterWidth)] body
        let rest ← elaborateCode resultWidth terminator outer ((result.name, w) :: scope) rest
        return .letRegion arg.var body rest
    | .unsupported form => throw (.unsupported form)

end Silmaril.MLIR.Frontend.Arith
