module

/-! # Integer affine maps and a pure, single-block `affine.for`

This slice uses mathematical integers for `index`. Bounds have one result,
the step is a positive constant, and `affine.yield` supplies the next carried
tuple. The single block is given by its pure denotation.
-/

@[expose] public section

namespace Silmaril.MLIR.Affine

universe u

/-- Affine expressions with separate dimension and symbol operands. -/
inductive Expr (dims symbols : Nat) where
  | const (value : Int)
  | dim (i : Fin dims)
  | symbol (i : Fin symbols)
  | add (lhs rhs : Expr dims symbols)
  | mulConst (factor : Int) (arg : Expr dims symbols)

def Expr.eval {dims symbols : Nat} (d : Fin dims → Int) (s : Fin symbols → Int) :
    Expr dims symbols → Int
  | .const value => value
  | .dim i => d i
  | .symbol i => s i
  | .add lhs rhs => lhs.eval d s + rhs.eval d s
  | .mulConst factor arg => factor * arg.eval d s

/-- An ordered tuple of affine result expressions. -/
abbrev Map (dims symbols results : Nat) := Fin results → Expr dims symbols

def Map.eval {dims symbols results : Nat} (map : Map dims symbols results)
    (d : Fin dims → Int) (s : Fin symbols → Int) : Fin results → Int :=
  fun i => (map i).eval d s

/-- `affine.apply` takes a single-result map. -/
def apply {dims symbols : Nat} (map : Map dims symbols 1)
    (d : Fin dims → Int) (s : Fin symbols → Int) : Int :=
  map.eval d s 0

abbrev Step := { n : Nat // 0 < n }

/-- One block takes the induction value and the carried tuple. The result
models the operands of its `affine.yield`. -/
structure Block (State : Type u) where
  yield : Int → State → State

/-- `affine.for` with single-result bounds, a constant positive step, and a
type shared by the initial, carried, yielded, and final values. -/
structure ForLoop (dims symbols : Nat) (State : Type u) where
  lower : Expr dims symbols
  upper : Expr dims symbols
  step : Step
  body : Block State

/-- The source loop either returns its current state or runs the body and
continues with the yielded state. The upper bound is exclusive. -/
inductive Runs {State : Type u} (upper : Int) (step : Step) (body : Block State) :
    Int → State → State → Prop where
  | done {iv : Int} {state : State} (stop : upper ≤ iv) : Runs upper step body iv state state
  | next {iv : Int} {state out : State} (enter : iv < upper)
      (rest : Runs upper step body (iv + (step.val : Int)) (body.yield iv state) out) :
      Runs upper step body iv state out

def ForLoop.Runs {dims symbols : Nat} {State : Type u} (loop : ForLoop dims symbols State)
    (d : Fin dims → Int) (s : Fin symbols → Int) (init out : State) : Prop :=
  Affine.Runs (loop.upper.eval d s) loop.step loop.body (loop.lower.eval d s) init out

/-- Enumerate the induction values independently of the carried state. -/
def iterationValues (upper : Int) (step : Step) (iv : Int) : List Int :=
  if iv < upper then iv :: iterationValues upper step (iv + (step.val : Int)) else []
termination_by (upper - iv).toNat
decreasing_by
  have := step.property
  omega

/-- Lower the loop to an ordered fold over its finite induction values. -/
def ForLoop.fold {dims symbols : Nat} {State : Type u} (loop : ForLoop dims symbols State)
    (d : Fin dims → Int) (s : Fin symbols → Int) (init : State) : State :=
  let indices := iterationValues (loop.upper.eval d s) loop.step (loop.lower.eval d s)
  indices.foldl (fun state iv => loop.body.yield iv state) init

end Silmaril.MLIR.Affine
