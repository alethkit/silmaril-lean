module

import Silmaril.SSA.SeaOfNodes.Diamond.PhiElim.Thms

namespace Silmaril.SSA.SeaOfNodes.Diamond.PhiElim

open RVSDG (Origin Tuple)

private abbrev int : ValueSort Unit := .data ()

private inductive Arithmetic : Signature Unit where
  | increment : Arithmetic [int] int

private def model : Model Arithmetic where
  value _ := Int
  run | .increment, .cons x .nil => Int.add x 1

private abbrev inputs := dataPorts ([.predicate, int] : List (ValueSort Unit))
private abbrev sigs : List (List (Ty Unit)) := [[.value int], [.value int]]
private abbrev Wire := Origin inputs sigs (.value int)

private def table : Dataflow Arithmetic inputs [] sigs :=
  .cons .increment (.cons (.arg (.tail .head)) .nil)
    (.cons .increment (.cons (.arg (.tail .head)) .nil) .nil)

private def firstProducer : Wire := .output (0 : Fin 2) .head
private def secondProducer : Wire := .output (1 : Fin 2) .head

private def diamond (first : Projection) (onTrue onFalse : Wire) :
    Graph Arithmetic [.predicate, int] sigs int where
  dataflow := table
  predicate := .arg .head
  phi := ⟨⟨first⟩, match first with
    | .onTrue => fun | .first => onTrue | .second => onFalse
    | .onFalse => fun | .first => onFalse | .second => onTrue⟩

private def straight : Pure.Program Arithmetic [.predicate, int] int :=
  { dataflow := table, result := firstProducer }

private def input (predicate : Bool) : Tuple (Val model.value) inputs :=
  .cons ⟨predicate⟩ (.cons (7 : Int) .nil)

example : eliminate (diamond .onTrue firstProducer firstProducer) = some straight := rfl
example : eliminate (diamond .onFalse firstProducer firstProducer) = some straight := rfl

-- Both producers compute the same value. Their structural addresses differ,
-- and reversing the Region order swaps the two rejected operand positions.
example : eliminate (diamond .onTrue firstProducer secondProducer) = none := rfl
example : eliminate (diamond .onFalse firstProducer secondProducer) = none := rfl

example : (diamond .onTrue firstProducer secondProducer).denote model (input true) =
    (diamond .onTrue firstProducer secondProducer).denote model (input false) := rfl

private theorem accepted_returns (first : Projection) (predicate : Bool)
    (success : eliminate (diamond first firstProducer firstProducer) = some straight) :
    (diamond first firstProducer firstProducer).Returns model (input predicate) (8 : Int) :=
  (returns_iff _ model success (input predicate) (8 : Int)).mpr rfl

example : (diamond .onTrue firstProducer firstProducer).Returns model (input true) (8 : Int) :=
  accepted_returns .onTrue true rfl
example : (diamond .onTrue firstProducer firstProducer).Returns model (input false) (8 : Int) :=
  accepted_returns .onTrue false rfl
example : (diamond .onFalse firstProducer firstProducer).Returns model (input true) (8 : Int) :=
  accepted_returns .onFalse true rfl
example : (diamond .onFalse firstProducer firstProducer).Returns model (input false) (8 : Int) :=
  accepted_returns .onFalse false rfl

example : (diamond .onFalse firstProducer firstProducer).lower.run model.toRVSDG (input false) =
    straight.lower.run (Pure.toRVSDGModel model) (input false) :=
  lower_run_eq (diamond .onFalse firstProducer firstProducer) model (p := straight) rfl (input false)

end Silmaril.SSA.SeaOfNodes.Diamond.PhiElim
