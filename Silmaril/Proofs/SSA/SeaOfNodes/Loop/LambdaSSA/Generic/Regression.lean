module

import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Thms

namespace Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic

open Diamond (Model Val ValueSort dataPorts)
open Diamond.LambdaSSA (inputEnv instruction)
open RVSDG (Tuple)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

private abbrev nat : ValueSort Unit := .data ()

private inductive Counter : Diamond.Signature Unit where
  | nonzero : Counter [nat] .predicate
  | decrement : Counter [nat] nat
  | flip : Counter [.predicate] .predicate

private def arithmetic : Model Counter where
  value _ := Nat
  run
    | .nonzero, .cons n .nil => ⟨Nat.blt 0 n⟩
    | .decrement, .cons n .nil => Nat.pred n
    | .flip, .cons b .nil => ⟨!b.down⟩

-- The loop carries a natural and a predicate. Its return reads an old Phi
-- directly, and both feedback operands are produced by the header table.
private def toggle : Graph Counter [nat, .predicate] [nat, .predicate] []
    [[.value .predicate], [.value nat], [.value .predicate]] .predicate where
  preheader := .nil
  header := .cons .nonzero (.cons (.arg (.tail (.tail .head))) .nil)
    (.cons .decrement (.cons (.arg (.tail (.tail .head))) .nil)
      (.cons .flip (.cons (.arg (.tail (.tail (.tail .head)))) .nil) .nil))
  phiInputs
    | .entry => .cons (.arg .head) (.cons (.arg (.tail .head)) .nil)
    | .backedge => .cons (.output (1 : Fin 3) .head) (.cons (.output (2 : Fin 3) .head) .nil)
  predicate := .output (0 : Fin 3) .head
  result := .arg (.tail (.tail (.tail .head)))

private def args (count : Nat) : Tuple (Val arithmetic.value) (dataPorts [nat, .predicate]) :=
  .cons count (.cons ⟨false⟩ .nil)

private theorem toggle_run (count budget : Nat) (result : Bool)
    (computed : toggle.evalBackedges arithmetic budget (args count) = some ⟨result⟩) :
    Eval (instruction arithmetic) (inputEnv arithmetic (args count)) (lower toggle)
      (42 : Nat) 0 (packResult arithmetic (out := .predicate) ⟨result⟩) 42 :=
  (returns_iff toggle arithmetic (args count) 42 ⟨result⟩).mp
    ((toggle.returns_iff_evalBackedges arithmetic (args count) ⟨result⟩).mpr ⟨budget, computed⟩)

example : Eval (instruction arithmetic) (inputEnv arithmetic (args 0)) (lower toggle)
    (42 : Nat) 0 (.pair (.inr .unit) .unit) 42 := toggle_run 0 0 false (by cbv)

example : Eval (instruction arithmetic) (inputEnv arithmetic (args 3)) (lower toggle)
    (42 : Nat) 0 (.pair (.inl .unit) .unit) 42 := toggle_run 3 3 true (by cbv)

private def spin : Graph Counter [.predicate] [] [] [] .predicate where
  preheader := .nil
  header := .nil
  phiInputs
    | .entry => .nil
    | .backedge => .nil
  predicate := .arg .head
  result := .arg .head

private def on : Tuple (Val arithmetic.value) (dataPorts [.predicate]) := .cons ⟨true⟩ .nil

example (payload : Value (Diamond.LambdaSSA.Atom arithmetic)) :
    ¬ Eval (instruction arithmetic) (inputEnv arithmetic on) (lower spin) (42 : Nat) 0 payload 42 := by
  intro eval
  obtain ⟨result, returns, _⟩ := (lower_eval_iff spin arithmetic on 42 42 0 payload).mp eval
  exact spin.not_returns_of_backedge_invariant arithmetic on result (· = .nil) rfl
    (fun old same => same.symm ▸ ⟨.nil, rfl, rfl⟩) returns

end Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic
