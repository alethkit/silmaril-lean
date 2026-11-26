module

public import Silmaril.SSA.MLIR.WasmSSA.Defs

/-! A source evaluator for the typed, straight-line WasmSSA integer fragment. -/

@[expose] public section

namespace Silmaril.MLIR.WasmSSA

/-- Words indexed by their types. Function arguments are in declaration order.
The environment of scalar bindings holds the most recent binding first. -/
inductive Env : List IntType → Type where
  | nil : Env []
  | cons {t : IntType} {ts : List IntType} (word : BitVec t.width) (tail : Env ts) : Env (t :: ts)

def Env.get {ts : List IntType} {t : IntType} (env : Env ts) (ref : Ref ts t) : BitVec t.width :=
  match env, ref with
  | .cons word _, .here => word
  | .cons _ tail, .there ref => tail.get ref

/-- Arithmetic wraps to the operand width. Subtraction takes the left operand first. -/
def BinOp.eval {w : Nat} (op : BinOp) (lhs rhs : BitVec w) : BitVec w :=
  match op with
  | .add => lhs + rhs
  | .sub => lhs - rhs
  | .mul => lhs * rhs
  | .and => lhs &&& rhs
  | .or => lhs ||| rhs
  | .xor => lhs ^^^ rhs

def Rhs.eval {params Γ : List IntType} {t : IntType}
    (args : Env params) (values : Env Γ) : Rhs params Γ t → BitVec t.width
  | .const word => word
  | .localGet ref => args.get ref
  | .binary op lhs rhs => op.eval (values.get lhs) (values.get rhs)
  | .eqz input => if values.get input == 0 then 1 else 0
  | .lt sign lhs rhs =>
    let x := values.get lhs
    let y := values.get rhs
    let less := match sign with
      | .signed => decide (x.toInt < y.toInt)
      | .unsigned => decide (x.toNat < y.toNat)
    if less then 1 else 0
  | .select condition ifTrue ifFalse =>
    if values.get condition = 0 then values.get ifFalse else values.get ifTrue

def Block.eval {params Γ : List IntType} {result : IntType} (args : Env params)
    (values : Env Γ) : Block params result Γ → BitVec result.width
  | .return_ ref => values.get ref
  | .letOp rhs rest => rest.eval args (.cons (rhs.eval args values) values)

def Func.eval {params : List IntType} {result : IntType} (f : Func params result)
    (args : Env params) : BitVec result.width := Block.eval args Env.nil f

end Silmaril.MLIR.WasmSSA
