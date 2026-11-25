module

public import Silmaril.Semantics.Operational.Determinism.Fuel.Defs
public import Silmaril.Semantics.Operational.Program.Defs

@[expose] public section

/-! # Closed Python integer bodies

The core models the body of an already entered, zero-argument function. Its
arithmetic and left-to-right evaluation follow the Python 3.12 language
reference (Expressions §§6.7 and 6.16, Simple statements §7.6).
-/

namespace Silmaril.Languages.Python.Core

open Semantics.Operational

inductive BinOp where
  | add
  | floorDiv
  deriving DecidableEq, Repr

inductive Expr where
  | int (value : Int)
  | binary (op : BinOp) (left right : Expr)
  deriving DecidableEq, Repr

/-- The elaboration target for a closed function body consisting of one return. -/
structure Body where
  value : Expr
  deriving DecidableEq, Repr

inductive Exception where
  | zeroDivisionError
  deriving DecidableEq, Repr

/-- Normal return or an uncaught Python exception. -/
abbrev Completion := Except Exception Int

inductive BinOp.Eval : BinOp → Int → Int → Completion → Prop where
  | add (left right : Int) : Eval .add left right (.ok (left + right))
  | div (left right : Int) (nonzero : right ≠ 0) :
      Eval .floorDiv left right (.ok (left.fdiv right))
  | divZero (left : Int) : Eval .floorDiv left 0 (.error .zeroDivisionError)

def BinOp.eval : BinOp → Int → Int → Completion
  | .add, left, right => .ok (left + right)
  | .floorDiv, left, right =>
      if right = 0 then .error .zeroDivisionError else .ok (left.fdiv right)

/-- A structural specification of the result of evaluating a closed expression. -/
def Expr.eval : Expr → Completion
  | .int value => .ok value
  | .binary op left right =>
      left.eval.bind fun a => right.eval.bind fun b => op.eval a b

/-- Left-to-right contexts propagate an arithmetic exception out of the expression. -/
inductive Expr.Step : Expr → Except Exception Expr → Prop where
  | left {op : BinOp} {left right : Expr} {next : Except Exception Expr} :
      Step left next → Step (.binary op left right) (next.map fun e => .binary op e right)
  | right {op : BinOp} {left : Int} {right : Expr} {next : Except Exception Expr} :
      Step right next → Step (.binary op (.int left) right) (next.map (.binary op (.int left)))
  | compute {op : BinOp} {left right : Int} {result : Completion} :
      op.Eval left right result → Step (.binary op (.int left) (.int right)) (result.map .int)

inductive State where
  | returning (expr : Expr)
  | raising (error : Exception)
  | finished (result : Completion)
  deriving Repr

def State.resume : Except Exception Expr → State
  | .ok expr => .returning expr
  | .error error => .raising error

def Body.start (body : Body) : State := .returning body.value

/-- Expression reductions are silent. Exiting the body emits its completion. -/
inductive Step : State → Option Completion → State → Prop where
  | expr {expr : Expr} {next : Except Exception Expr} :
      expr.Step next → Step (.returning expr) none (State.resume next)
  | ret (value : Int) : Step (.returning (.int value)) (some (.ok value)) (.finished (.ok value))
  | raise (error : Exception) : Step (.raising error) (some (.error error)) (.finished (.error error))

inductive Observes : State → Outcome Completion → Prop where
  | finished (result : Completion) : Observes (.finished result) (.returned result)

def ordinary : OpSem State Completion where
  step source target := ∃ label, Step source label target
  observe := Observes

/-- Statically enabled primitive operations. Literals and return are always enabled. -/
structure Profile where
  add : Bool
  floorDiv : Bool

def Profile.arithmetic : Profile := ⟨true, true⟩
def Profile.addition : Profile := ⟨true, false⟩

def Profile.allows (profile : Profile) : BinOp → Bool
  | .add => profile.add
  | .floorDiv => profile.floorDiv

def Profile.supports (profile : Profile) : Expr → Bool
  | .int _ => true
  | .binary op left right => profile.allows op && profile.supports left && profile.supports right

def State.supported (profile : Profile) : State → Bool
  | .returning expr => profile.supports expr
  | .raising _ | .finished _ => true

/-- Passing an unsupported state directly to the policy reaches the profile's UB marker. -/
def semantics (profile : Profile) : WithUB State Completion :=
  (WithUB.ofOpSem ordinary).enforce (State.supported profile ·)

def labelled (profile : Profile) : Labelled State Completion Completion where
  step source label target := source.supported profile ∧ Step source label target
  observe := (semantics profile).observe

/-- Static rejection at entry leaves no initial state. -/
def model (profile : Profile) : HasOpSem Body State Completion where
  initial body state := profile.supports body.value ∧ state = body.start
  semantics := semantics profile

def Body.start? (profile : Profile) (body : Body) : Option State :=
  if profile.supports body.value then some body.start else none

/-- A one-redex selector; literals need no expression step. -/
def Expr.reduce : Expr → Option (Except Exception Expr)
  | .int _ => none
  | .binary op left right =>
      match left with
      | .int a =>
          match right with
          | .int b => some ((op.eval a b).map .int)
          | .binary .. => right.reduce.map (·.map (.binary op (.int a)))
      | .binary .. => left.reduce.map (·.map fun e => .binary op e right)

/-- Compute a labelled transition, if any, by inspecting the current state. -/
def State.advance : State → Option (Option Completion × State)
  | .returning (.int value) => some (some (.ok value), .finished (.ok value))
  | .returning expr@(.binary ..) => expr.reduce.map fun next => (none, State.resume next)
  | .raising error => some (some (.error error), .finished (.error error))
  | .finished _ => none

def State.pick (source : State) : Decision State Completion :=
  match source with
  | .finished result => .stop (.observed (.returned result))
  | _ => source.advance.elim (.stop .stuck) fun transition => .move transition.2

/-- Count unreduced binary operations. -/
def Expr.work : Expr → Nat
  | .int _ => 0
  | .binary _ left right => left.work + right.work + 1

/-- A decreasing measure and a sufficient transition budget. -/
def State.budget : State → Nat
  | .returning expr => expr.work + 2
  | .raising _ => 1
  | .finished _ => 0

/-- The structural result specification extended to intermediate states. -/
def State.result : State → Completion
  | .returning expr => expr.eval
  | .raising error => .error error
  | .finished result => result

end Silmaril.Languages.Python.Core
