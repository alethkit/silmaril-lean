module

import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Reindex.Thms

namespace Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic

open Diamond (Model Val ValueSort dataPorts)
open Diamond.LambdaSSA (Atom encodeTuple inputEnv instruction terminatorRegion)
open SeaOfNodes.Loop (Incoming)
open RVSDG (Tuple)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)
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

example : (lower toggle).HasType (inputContext [nat, .predicate]) [packed [.value .predicate]] :=
  lower_hasType toggle

private def entryFirst : Fin 2 ≃ Incoming where
  toFun := Fin.cases .entry (fun _ => .backedge)
  invFun := Incoming.select 0 1
  left_inv := by
    intro i
    refine Fin.cases rfl (fun j => ?_) i
    have same : j = 0 := Fin.fin_one_eq_zero j
    cases same
    rfl
  right_inv := fun arrival => by cases arrival <;> rfl

private def swapIncoming : Incoming ≃ Incoming where
  toFun := Incoming.select .backedge .entry
  invFun := Incoming.select .backedge .entry
  left_inv := fun arrival => by cases arrival <;> rfl
  right_inv := fun arrival => by cases arrival <;> rfl

private def forward : Fin 2 ≃ HeaderIncoming toggle :=
  entryFirst.trans (headerIncomingEquiv toggle)

private def reversed : Fin 2 ≃ HeaderIncoming toggle :=
  (entryFirst.trans swapIncoming).trans (headerIncomingEquiv toggle)

-- Reversing the positions preserves each original branch and its scope.
example : slotBranch toggle reversed 0 = slotBranch toggle forward 1 := rfl
example : slotBranch toggle reversed 1 = slotBranch toggle forward 0 := rfl

example : slotBranch toggle reversed 0 = .br 0 (.pair (.var 2) (.pair (.var 1) .unit)) := rfl
example : slotBranch toggle reversed 1 = .br 0 (.pair (.var 0) (.pair (.var 1) .unit)) := rfl

example : entry toggle = terminatorRegion (slotBranch toggle reversed 1) := rfl

example : slotBranch toggle reversed (reversed.symm (headerIncoming toggle .backedge)) =
    .br 0 (edge toggle .backedge).argument :=
  slot_branch_roundtrip toggle reversed (headerIncoming toggle .backedge)

private def feedback : Tuple (Val arithmetic.value) (dataPorts [nat, .predicate]) :=
  .cons (0 : Nat) (.cons ⟨true⟩ .nil)

-- The scheduled values are the true test, the decremented natural and the
-- flipped predicate. The true case then extends that environment by unit.
private def feedbackEnv : Env (Atom arithmetic) :=
  let decoded := unpackEnv arithmetic (args 1) (inputEnv arithmetic (args 1))
  let tested := extend decoded (.inl .unit)
  let decremented := extend tested (.atom ⟨(), (0 : Nat)⟩)
  let flipped := extend decremented (.inl .unit)
  extend flipped .unit

example : Eval (instruction arithmetic) (inputEnv arithmetic (args 1))
    (terminatorRegion (slotBranch toggle reversed 1)) (42 : Nat) 0 (encodeTuple arithmetic (args 1)) 42 :=
  (slot_transfer_iff toggle arithmetic reversed 1 _ 42 42 0 _).mpr ⟨rfl, rfl, rfl⟩

example : Eval (instruction arithmetic) feedbackEnv
    (terminatorRegion (slotBranch toggle reversed 0)) (42 : Nat) 0 (encodeTuple arithmetic feedback) 42 :=
  (slot_transfer_iff toggle arithmetic reversed 0 feedbackEnv 42 42 0 _).mpr ⟨rfl, rfl, rfl⟩

private abbrev HeaderReturns (next : Tuple (Val arithmetic.value) (dataPorts [nat, .predicate])) :=
  Eval (instruction arithmetic) (extend (inputEnv arithmetic (args 1)) (encodeTuple arithmetic (args 1)))
    (header toggle) (42 : Nat) 0 (encodeTuple arithmetic next) 42

example : HeaderReturns feedback :=
  (header_backedge_iff toggle arithmetic (args 1) (args 1) feedback 42 42).mpr ⟨rfl, rfl⟩

-- Reading the predicate from entry or the natural from the old tuple
-- while taking feedback would yield one of these mixed packets.
example : ¬ HeaderReturns (args 0) := by
  intro run
  have mixed := ((header_backedge_iff toggle arithmetic (args 1) (args 1) (args 0) 42 42).mp run).1
  have impossible : Sum.inr feedback = Sum.inr (args 0) := mixed
  cases impossible

example : ¬ HeaderReturns (.cons (1 : Nat) (.cons ⟨true⟩ .nil)) := by
  intro run
  have mixed := ((header_backedge_iff toggle arithmetic (args 1) (args 1) _ 42 42).mp run).1
  have impossible : Sum.inr feedback = Sum.inr (.cons (1 : Nat) (.cons ⟨true⟩ .nil)) := mixed
  cases impossible

example : Eval (instruction arithmetic) (inputEnv arithmetic (args 1)) (lower toggle)
    (42 : Nat) 0 (.pair (.inl .unit) .unit) 42 := toggle_run 1 1 true (by cbv)

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
