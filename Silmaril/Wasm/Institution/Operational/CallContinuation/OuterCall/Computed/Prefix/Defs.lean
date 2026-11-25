module

public import Silmaril.Wasm.Execution.Runtime
public import Silmaril.Wasm.Numerics.Integer

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix

open Execution.Runtime (Value)

inductive Op where
  | get (idx : LocalIdx)
  | bin (kind : IntType) (op : IntBinOp)

/-- The evaluation stack is in instruction order, with the rightmost operand on top. -/
inductive Outcome where
  | values (stack : List Value)
  | trap (saved : List Value)

/-- A prefix head reduces independently of the pending instruction sequence. -/
inductive Reduce (locals : List Value) : List Value → Op → Outcome → Prop where
  | get {stack : List Value} {i : LocalIdx} {v : Value}
      (found : locals[i.toNat]? = some v) :
      Reduce locals stack (.get i) (.values (stack ++ [v]))
  | bin {stack : List Value} {t : IntType} {op : IntBinOp} {x y z : BitVec t.width}
      (ok : Numerics.intBinOp t op x y = .ok z) :
      Reduce locals (stack ++ [.int t x, .int t y]) (.bin t op) (.values (stack ++ [.int t z]))
  | trap {stack : List Value} {t : IntType} {op : IntBinOp} {x y : BitVec t.width}
      {cause : Numerics.IntTrap} (err : Numerics.intBinOp t op x y = .error cause) :
      Reduce locals (stack ++ [.int t x, .int t y]) (.bin t op) (.trap stack)

/-- A trap step drops an adjacent, nonempty portion of its context. -/
inductive Discard {A : Type} : List Value → List A → List Value → List A → Prop where
  | cut (kept removed : List Value) (cut rest : List A) (nonempty : removed ≠ [] ∨ cut ≠ []) :
      Discard (kept ++ removed) (cut ++ rest) kept rest

/-- A single checker instruction acts on a top-first type stack. -/
def checkOp (locals : List NumType) (stack : List NumType) : Op → Option (List NumType)
  | .get i => (locals[i.toNat]?).map (· :: stack)
  | .bin t _ =>
    match stack with
    | right :: left :: rest =>
      if left = .int t ∧ right = .int t then some (.int t :: rest) else none
    | _ => none

def check (locals : List NumType) (stack : List NumType) : List Op → Option (List NumType)
  | [] => some stack
  | op :: rest => (checkOp locals stack op).bind fun next => check locals next rest

def stackTypes (stack : List Value) : List NumType := (stack.map Value.type).reverse

/-- The residual prefix consumes the current values and produces exactly the
callee parameter types in source evaluation order. -/
def WellTyped (locals stack : List Value) (code : List Op) (result : List NumType) : Prop :=
  check (locals.map Value.type) (stackTypes stack) code = some result.reverse

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix
