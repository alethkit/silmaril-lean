module

import Silmaril.SSA.SeaOfNodes.Diamond.Institution.Thms
meta import Silmaril.SSA.SeaOfNodes.Diamond.Institution.Defs

namespace Silmaril.SSA.SeaOfNodes.Diamond.Institution

open CategoryTheory
open RVSDG (Tuple)

private abbrev word : ValueSort Unit := .data ()
private abbrev inputs : List (ValueSort Unit) := [.predicate, word]
private abbrev sigs : List (List (Ty Unit)) := [[.value word], [.value word]]

private inductive Arithmetic : Diamond.Signature.{0, 0} Unit
  | inc : Arithmetic [word] word
  | double : Arithmetic [word] word

private abbrev sig : Signature.{0, 0} Unit := ⟨Arithmetic⟩

private def arithmetic : Model.{0, 0, 0} sig.op where
  value _ := Nat
  run
    | .inc, .cons n .nil => Nat.succ n
    | .double, .cons n .nil => Nat.add n n

private def swap : sig ⟶ sig :=
  ⟨fun
    | .inc => .double
    | .double => .inc⟩

private def diamond (onTrue onFalse : Arithmetic [word] word) : Graph sig.op inputs sigs word where
  dataflow :=
    .cons onTrue (.cons (.arg (.tail .head)) .nil)
      (.cons onFalse (.cons (.arg (.tail .head)) .nil) .nil)
  predicate := .arg .head
  phi := ⟨⟨.onFalse⟩, fun
    | .first => .output (1 : Fin 2) .head
    | .second => .output (0 : Fin 2) .head⟩

private def entry (pred : Bool) : Tuple (Val arithmetic.value) (dataPorts inputs) :=
  .cons ⟨pred⟩ (.cons (4 : Nat) .nil)

private def graph := diamond .inc .double

/-- info: [5, 8, 8, 5] -/
#guard_msgs in
#eval ([graph.denote arithmetic (entry true), graph.denote arithmetic (entry false),
  (mapGraph swap graph).denote arithmetic (entry true),
  (mapGraph swap graph).denote arithmetic (entry false)] : List Nat)

example : graph.denote (reduct swap arithmetic) (entry true) = (8 : Nat) := rfl
example : graph.denote (reduct swap arithmetic) (entry false) = (5 : Nat) := rfl

private def identify : sig ⟶ sig :=
  ⟨fun
    | .inc => .inc
    | .double => .inc⟩

private def sentence : Equation sig :=
  ⟨inputs, word, sigs, sigs, graph, diamond .double .inc⟩

example : ¬ sentence.Holds arithmetic := by
  intro holds
  have distinct := holds (entry true)
  change (5 : Nat) = 8 at distinct
  cases distinct

example : (sentence.map identify).Holds arithmetic :=
  (sentence.satisfaction identify arithmetic).mpr (fun _ => rfl)

example : (sentence.map swap).map swap = sentence := by
  rw [← Equation.map_comp]
  rfl

example : ((inst.{0, 0, 0} Unit).I.map swap).sen sentence = sentence.map swap := rfl

example : (((inst.{0, 0, 0} Unit).I.map swap).mod.obj (Discrete.mk arithmetic)).as =
    reduct swap arithmetic := rfl

end Silmaril.SSA.SeaOfNodes.Diamond.Institution
