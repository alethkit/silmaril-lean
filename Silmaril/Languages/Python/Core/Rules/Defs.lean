module

public import Silmaril.Languages.Python.Core.Defs
public import Silmaril.Semantics.SOS.Defs

/-! # Positive ground rules for closed Python arithmetic

A finite family of schemas generates rules over exact integers and closed core
syntax. Context rules require a subexpression judgment, while contraction
requires a primitive arithmetic judgment. Whole-body steps use expression
premises or the facts for return and uncaught exceptions.
-/

@[expose] public section

namespace Silmaril.Languages.Python.Core.Rules

open Semantics.SOS (Rule)

/-- Arithmetic, expression reductions and labelled body transitions have distinct names. -/
inductive Judgment where
  | primitive (op : BinOp) (left right : Int) (result : Completion)
  | expression (source : Expr) (result : Except Exception Expr)
  | edge (source : State) (label : Option Completion) (target : State)

/-- Each constructor supplies the premise list and conclusion of a ground instance. -/
inductive Schema : Rule Judgment → Prop where
  | add (left right : Int) :
      Schema ⟨[], .primitive .add left right (.ok (left + right))⟩
  | div (left right : Int) (nonzero : right ≠ 0) :
      Schema ⟨[], .primitive .floorDiv left right (.ok (left.fdiv right))⟩
  | divZero (left : Int) :
      Schema ⟨[], .primitive .floorDiv left 0 (.error .zeroDivisionError)⟩
  | left (op : BinOp) (left right : Expr) (next : Except Exception Expr) :
      Schema ⟨[.expression left next],
        .expression (.binary op left right) (next.map fun expr => .binary op expr right)⟩
  | right (op : BinOp) (left : Int) (right : Expr) (next : Except Exception Expr) :
      Schema ⟨[.expression right next],
        .expression (.binary op (.int left) right) (next.map (.binary op (.int left)))⟩
  | compute (op : BinOp) (left right : Int) (result : Completion) :
      Schema ⟨[.primitive op left right result],
        .expression (.binary op (.int left) (.int right)) (result.map .int)⟩
  | evalValue (source next : Expr) :
      Schema ⟨[.expression source (.ok next)], .edge (.returning source) none (.returning next)⟩
  | evalError (source : Expr) (error : Exception) :
      Schema ⟨[.expression source (.error error)], .edge (.returning source) none (.raising error)⟩
  | ret (value : Int) :
      Schema ⟨[], .edge (.returning (.int value)) (some (.ok value)) (.finished (.ok value))⟩
  | raise (error : Exception) :
      Schema ⟨[], .edge (.raising error) (some (.error error)) (.finished (.error error))⟩

def rules : Set (Rule Judgment) := {rule | Schema rule}

abbrev Derives := Semantics.SOS.Derives rules

end Silmaril.Languages.Python.Core.Rules
