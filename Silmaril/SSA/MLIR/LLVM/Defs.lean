module

public import Silmaril.SSA.MLIR.Arith.Defs

/-! # Concrete scalar LLVM dialect blocks

The candidate syntax uses typed references and separates admission of a whole
block from execution on a concrete environment.
-/

@[expose] public section

namespace Silmaril.MLIR.LLVM

open Arith (Env Var Width)

inductive BinOp where
  | add
  | sub
  | mul
  | udiv
  deriving DecidableEq, Repr

inductive Flag where
  | nsw
  | nuw
  | exact
  deriving DecidableEq, Repr

inductive AdmissionError where
  | unsupportedWidth (bits : Nat)
  | excludedFlags (op : BinOp) (flags : List Flag)
  | poison
  | undef
  | unsupportedOp (name : String)
  | unsupportedTerminator (name : String)
  deriving DecidableEq, Repr

inductive ImmediateUB where
  | divisionByZero
  deriving DecidableEq, Repr

/-- Binary operations on defined operands. The flag-free quotient is unsigned. -/
def BinOp.eval (op : BinOp) {bits : Nat} (lhs rhs : BitVec bits) :
    Except ImmediateUB (BitVec bits) :=
  match op with
  | .add => .ok (lhs + rhs)
  | .sub => .ok (lhs - rhs)
  | .mul => .ok (lhs * rhs)
  | .udiv => if rhs = 0 then .error .divisionByZero else .ok (lhs / rhs)

namespace Syntax

/-- Decoded scalar RHS candidates. Other operations or attributes can be
reported by the caller as `unsupported`; this interface has no text parser. -/
inductive Rhs (Γ : List Width) (w : Width) where
  | constant (value : BitVec w.val)
  | binary (op : BinOp) (flags : List Flag) (lhs rhs : Var Γ w)
  | poison
  | undef
  | unsupported (name : String)

/-- A candidate body with a single block and a single declared scalar result. -/
inductive Block : List Width → Width → Type where
  | ret {Γ : List Width} {w : Width} (value : Var Γ w) : Block Γ w
  | letOp {Γ : List Width} {v w : Width} (rhs : Rhs Γ v) (rest : Block (v :: Γ) w) :
      Block Γ w
  | unsupportedTerminator {Γ : List Width} {w : Width} (name : String) : Block Γ w

end Syntax

/-- Instructions available to the evaluator after the syntax check. -/
inductive Rhs (Γ : List Width) (w : Width) where
  | constant (value : BitVec w.val)
  | binary (op : BinOp) (lhs rhs : Var Γ w)

inductive Block : List Width → Width → Type where
  | ret {Γ : List Width} {w : Width} (value : Var Γ w) : Block Γ w
  | letOp {Γ : List Width} {v w : Width} (rhs : Rhs Γ v) (rest : Block (v :: Γ) w) :
      Block Γ w

/-- `Width` already requires positivity. LLVM IR allows up to `2^23` bits. -/
def widthSupported (w : Width) : Bool := decide (w.val ≤ 2 ^ 23)

def Syntax.Rhs.admit {Γ : List Width} {w : Width} : Syntax.Rhs Γ w →
    Except AdmissionError (LLVM.Rhs Γ w)
  | .constant value => .ok (.constant value)
  | .binary op [] lhs rhs => .ok (.binary op lhs rhs)
  | .binary op flags _ _ => .error (.excludedFlags op flags)
  | .poison => .error .poison
  | .undef => .error .undef
  | .unsupported name => .error (.unsupportedOp name)

/-- Check argument and binding widths and admit every instruction and the
terminator. The return reference already has the declared result width. -/
def Syntax.Block.admit {Γ : List Width} {w : Width} (block : Syntax.Block Γ w) :
    Except AdmissionError (LLVM.Block Γ w) :=
  match Γ.find? (fun width => !widthSupported width) with
  | some width => .error (.unsupportedWidth width.val)
  | none => admitBody block
where
  admitBody {Γ : List Width} {w : Width} : Syntax.Block Γ w →
      Except AdmissionError (LLVM.Block Γ w)
    | .ret value => .ok (.ret value)
    | .letOp (v := v) rhs rest => do
        if !widthSupported v then throw (.unsupportedWidth v.val)
        let rhs ← rhs.admit
        let rest ← admitBody rest
        pure (.letOp rhs rest)
    | .unsupportedTerminator name => .error (.unsupportedTerminator name)

def Rhs.eval {Γ : List Width} {w : Width} (rhs : Rhs Γ w) (env : Env Γ) :
    Except ImmediateUB (BitVec w.val) :=
  match rhs with
  | .constant value => .ok value
  | .binary op lhs rhs => op.eval (env.get lhs) (env.get rhs)

/-- Evaluate in program order, including bindings unused by the return. The
observation is a returned bitvector or immediate UB. -/
def Block.eval {Γ : List Width} {w : Width} : Block Γ w → Env Γ →
    Except ImmediateUB (BitVec w.val)
  | .ret value, env => .ok (env.get value)
  | .letOp rhs rest, env => do
      let value ← rhs.eval env
      rest.eval (.cons value env)

/-- The outer result reports admission; only an admitted block has an execution
outcome. The environment supplies a concrete bitvector for each argument. -/
def Syntax.Block.run {Γ : List Width} {w : Width} (block : Syntax.Block Γ w) (env : Env Γ) :
    Except AdmissionError (Except ImmediateUB (BitVec w.val)) :=
  block.admit.map (fun admitted => admitted.eval env)

/-- Translate a primitive shared by the LLVM and arithmetic slices. -/
def Rhs.toArith {Γ : List Width} {w : Width} : Rhs Γ w → Option (Arith.Rhs Γ w)
  | .constant value => some (.constant value)
  | .binary .add lhs rhs => some (.binary .addi lhs rhs)
  | .binary .mul lhs rhs => some (.binary .muli lhs rhs)
  | .binary .sub .. | .binary .udiv .. => none

/-- Translate the common constant/add/mul/return fragment. Subtraction and
division have no corresponding primitive in the arithmetic slice. -/
def Block.toArith {Γ : List Width} {w : Width} : Block Γ w → Option (Arith.Block Γ w)
  | .ret value => some (.yield value)
  | .letOp rhs rest => do
      let rhs ← rhs.toArith
      let rest ← rest.toArith
      pure (.letOp rhs rest)

end Silmaril.MLIR.LLVM
