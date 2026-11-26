module

import Silmaril.SSA.SeaOfNodes.Loop.Institution.Thms

namespace Silmaril.SSA.SeaOfNodes.Loop.Institution

open CategoryTheory
open Diamond (Model Ty Val ValueSort dataPorts)
open Diamond.Institution (Signature reduct)
open RVSDG (Tuple)

private abbrev word : ValueSort Unit := .data ()
private abbrev wordPort : Ty Unit := .value word
private abbrev predicatePort : Ty Unit := .value .predicate

private inductive Primitive : Diamond.Signature.{0, 0} Unit where
  | zero : Primitive [] word
  | nonzero : Primitive [word] .predicate
  | alwaysTrue : Primitive [word] .predicate

private abbrev sig : Signature.{0, 0} Unit := ⟨Primitive⟩

private def arithmetic : Model.{0, 0, 0} sig.op where
  value _ := Nat
  run
    | .zero, .nil => (0 : Nat)
    | .nonzero, .cons n .nil => ⟨(show Nat from n) != 0⟩
    | .alwaysTrue, .cons _ .nil => ⟨true⟩

private def forceTrue : sig ⟶ sig :=
  ⟨fun
    | .zero => .zero
    | .nonzero => .alwaysTrue
    | .alwaysTrue => .alwaysTrue⟩

private def reset (guard : Primitive [word] .predicate) : Program sig [word] word where
  carried := [word]
  entrySigs := []
  headerSigs := [[predicatePort], [wordPort]]
  graph :=
    { preheader := .nil
      header := .cons guard (.cons (.arg (.tail .head)) .nil) (.cons .zero .nil .nil)
      phiInputs
        | .entry => .cons (.arg .head) .nil
        | .backedge => .cons (.output (1 : Fin 2) .head) .nil
      predicate := .output (0 : Fin 2) .head
      result := .arg (.tail .head) }

private def entry (n : Nat) : Tuple (Val arithmetic.value) (dataPorts [word]) :=
  .cons n .nil

private def check := reset .nonzero
private def spin := reset .alwaysTrue

private theorem mapCheck : check.map forceTrue = spin := rfl

private theorem returnsZero : check.graph.Returns arithmetic (entry 4) (0 : Nat) :=
  ⟨1, .backedge (next := entry 0) (by cbv) (.exit (by cbv))⟩

private theorem spinNeverReturns
    (input : Tuple (Val arithmetic.value) (dataPorts [word])) (result : Nat) :
    ¬ spin.graph.Returns arithmetic input result :=
  spin.graph.not_returns_of_backedge_invariant arithmetic input result (fun _ => True)
    trivial (fun old _ => by
      cases old with
      | cons n tail =>
        cases tail
        exact ⟨entry 0, rfl, trivial⟩)

private def equation : Equation sig := ⟨[word], word, check, spin⟩

private theorem equationFails : ¬ (Sentence.equation equation).Holds arithmetic := fun holds =>
  spinNeverReturns (entry 4) 0
    (((equation.holds_iff_returns arithmetic).mp holds (entry 4) (0 : Nat)).mp returnsZero)

-- After relabelling the two sides agree on the empty return relation.
private theorem mappedEquationHolds : ((Sentence.equation equation).map forceTrue).Holds arithmetic := by
  intro input
  rfl

private theorem reductEquationHolds : (Sentence.equation equation).Holds (reduct forceTrue arithmetic) :=
  ((Sentence.equation equation).satisfaction forceTrue arithmetic).mp mappedEquationHolds

private theorem checkTerminates : (Sentence.terminates check).Holds arithmetic := by
  apply (terminates_holds_iff_returns check arithmetic).mpr
  intro input
  cases input with
  | cons n tail =>
    cases tail
    cases n with
    | zero => exact ⟨(0 : Nat), 0, .exit (by cbv)⟩
    | succ n => exact ⟨(0 : Nat), 1, .backedge (next := entry 0) (by cbv) (.exit (by cbv))⟩

private theorem mappedCheckDoesNotTerminate :
    ¬ ((Sentence.terminates check).map forceTrue).Holds arithmetic := by
  intro holds
  change (Sentence.terminates (check.map forceTrue)).Holds arithmetic at holds
  rw [mapCheck] at holds
  obtain ⟨result, returns⟩ := (terminates_holds_iff_returns spin arithmetic).mp holds (entry 4)
  exact spinNeverReturns (entry 4) result returns

private theorem reductCheckDoesNotTerminate :
    ¬ (Sentence.terminates check).Holds (reduct forceTrue arithmetic) :=
  fun holds => mappedCheckDoesNotTerminate
    (((Sentence.terminates check).satisfaction forceTrue arithmetic).mpr holds)

end Silmaril.SSA.SeaOfNodes.Loop.Institution
