module

import Silmaril.SSA.PhiView.Thms

namespace Silmaril.SSA.PhiView

open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA (Terminator Tm)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

private instance : HasTy Empty (Ty Unit) := ⟨Empty.elim, Empty.elim⟩

private def word : Ty Unit := .base ()

private def tuple (x y : Nat) : Tm Empty := .pair (.var x) (.pair (.var y) .unit)

private inductive Site where
  | entry
  | header

private def terms : Site → Terminator Empty
  | .entry => .case (.var 0) (.br 0 (tuple 2 3)) (.br 0 (tuple 3 0))
  | .header => .br 0 (tuple 1 0)

private def context : Site → List (Ty Unit)
  | .entry => [.coprod word word, word, word]
  | .header => [word, word]

private def typing : SourceTyping (τ := Ty Unit) terms where
  context := context
  cases
    | .entry => .case (A := word) (B := word) (.var (i := 0) rfl) .jump .jump
    | .header => .jump

private def params : Nat → List (Ty Unit)
  | 0 => [word, word]
  | _ + 1 => []

private def two {Γ : List (Ty Unit)} (x y : Operand Γ word) : Arguments Γ [word, word] :=
  fun i => Fin.cases x (Fin.cases y (fun j => (Nat.not_lt_zero _ j.isLt).elim)) i

private def args : BlockArgs typing params := by
  intro ⟨site, occurrence⟩
  cases site with
  | entry =>
    cases occurrence with
    | left leaf =>
      cases leaf
      exact ⟨two ⟨2, rfl⟩ ⟨3, rfl⟩, rfl⟩
    | right leaf =>
      cases leaf
      exact ⟨two ⟨3, rfl⟩ ⟨0, rfl⟩, rfl⟩
  | header =>
    cases occurrence
    exact ⟨two ⟨1, rfl⟩ ⟨0, rfl⟩, rfl⟩

private def phis : View typing params := ofBlockArgs args

private def left : EdgeOcc terms := ⟨.entry, .left .jump⟩
private def right : EdgeOcc terms := ⟨.entry, .right .jump⟩
private def back : EdgeOcc terms := ⟨.header, .jump⟩

private def entryEnv (choice : Value Nat) : Env Nat
  | 0 => choice
  | 1 => .atom 11
  | 2 => .atom 29
  | _ + 3 => .unit

private def oldHeader : Env Nat
  | 0 => .atom 11
  | 1 => .atom 29
  | _ + 2 => .unit

private def state : Nat := 42

private def instr (op : Empty) : Value Nat → Nat → Value Nat → Nat → Prop := op.elim

private def pair (a b : Nat) : Value Nat := .pair (.atom a) (.pair (.atom b) .unit)

example : left.target = right.target := rfl
example : left ≠ right := fun h => by cases h

example : latch phis left (extend (entryEnv (.inl (.atom 17))) (.atom 17)) = pair 11 29 := rfl
example : latch phis right (extend (entryEnv (.inr (.atom 17))) (.atom 17)) = pair 29 17 := rfl

example :
    Eval instr (entryEnv (.inl (.atom 17)))
      (.case (.var 0) (.br left.target left.argument) (.br right.target right.argument))
      state 0 (pair 11 29) state :=
  .case_inl .var ((latch_eq_transfer instr phis left _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩)

example :
    Eval instr (entryEnv (.inr (.atom 17)))
      (.case (.var 0) (.br left.target left.argument) (.br right.target right.argument))
      state 0 (pair 29 17) state :=
  .case_inr .var ((latch_eq_transfer instr phis right _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩)

-- One backedge from the header to itself, after unpacking its old parameter.
example : latch phis back oldHeader = pair 29 11 := rfl

example : Eval instr oldHeader (.br back.target back.argument) state 0 (pair 29 11) state :=
  (latch_eq_transfer instr phis back _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

end Silmaril.SSA.PhiView
