module

import Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Institution.Fiber.Thms

namespace Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Institution

open CategoryTheory Silmaril.Logic.Institution
open Diamond.Institution (mapGraph reduct)
open RVSDG (Tuple)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

private abbrev word : ValueSort Unit := .data ()
private abbrev inputs : List (ValueSort Unit) := [.predicate, word]
private abbrev sigs : List (List (Ty Unit)) := [[.value word], [.value word]]

private inductive Arithmetic : Diamond.Signature Unit where
  | inc : Arithmetic [word] word
  | double : Arithmetic [word] word

private abbrev sig : Diamond.Institution.Signature Unit := ⟨Arithmetic⟩

private def arithmetic : Model Arithmetic where
  value _ := Nat
  run
    | .inc, .cons n .nil => Nat.succ n
    | .double, .cons n .nil => Nat.add n n

private def swap : sig ⟶ sig :=
  ⟨fun | .inc => .double | .double => .inc⟩

private def diamond (onTrue onFalse : Arithmetic [word] word) : Graph Arithmetic inputs sigs word where
  dataflow :=
    .cons onTrue (.cons (.arg (.tail .head)) .nil)
      (.cons onFalse (.cons (.arg (.tail .head)) .nil) .nil)
  predicate := .arg .head
  phi := ⟨⟨.onFalse⟩, fun
    | .first => .output (1 : Fin 2) .head
    | .second => .output (0 : Fin 2) .head⟩

private def graph := diamond .inc .double

private def entry (flag : Bool) : Tuple (Val arithmetic.value) (dataPorts inputs) :=
  .cons ⟨flag⟩ (.cons (4 : Nat) .nil)

-- Both occurrences still jump to label zero. The false arm remains the
-- first Region predecessor and latches the newest produced value.
example : edge (mapGraph swap graph) .first = edge graph .first := rfl
example : edge (mapGraph swap graph) .second = edge graph .second := rfl

example : edge (mapGraph swap graph) .first ≠ edge (mapGraph swap graph) .second :=
  (projections_distinct (mapGraph swap graph)).symm

example : ((lower graph).mapInstr (mapPrimitive swap)).HasType (initialContext inputs) [sortCode word] :=
  (lower_hasType graph).mapInstr (mapPrimitive swap) (mapPrimitive_preservesTypes swap)

example : (phiView (mapGraph swap graph)).table.branch (edge (mapGraph swap graph) .first) =
    .br 0 (.pair (.var 1) .unit) :=
  edge_branch (mapGraph swap graph) .first

example : (phiView (mapGraph swap graph)).table.branch (edge (mapGraph swap graph) .second) =
    .br 0 (.pair (.var 2) .unit) :=
  edge_branch (mapGraph swap graph) .second

private theorem runRelabelled (flag : Bool) (result : Nat)
    (expected : (mapGraph swap graph).denote arithmetic (entry flag) = result) :
    Eval (instruction arithmetic) (inputEnv arithmetic (entry flag))
      ((lower graph).mapInstr (mapPrimitive swap)) (42 : Nat) 0 (.atom ⟨(), result⟩) 42 := by
  rw [lower_map]
  exact (lower_eval_iff (mapGraph swap graph) arithmetic (entry flag) 42 42 0 _).mpr
    ⟨rfl, congrArg (encode arithmetic (sort := word)) expected.symm, rfl⟩

example : Eval (instruction arithmetic) (inputEnv arithmetic (entry true))
    ((lower graph).mapInstr (mapPrimitive swap)) (42 : Nat) 0 (.atom ⟨(), (8 : Nat)⟩) 42 :=
  runRelabelled true 8 rfl

example : Eval (instruction arithmetic) (inputEnv arithmetic (entry false))
    ((lower graph).mapInstr (mapPrimitive swap)) (42 : Nat) 0 (.atom ⟨(), (5 : Nat)⟩) 42 :=
  runRelabelled false 5 rfl

private def equation : Diamond.Institution.Equation sig :=
  ⟨inputs, word, sigs, sigs, graph, diamond .double .inc⟩

example : ((inst.{0, 0, 0} Unit).I.map swap).sen (lowerEquation equation) =
    lowerEquation (equation.map swap) :=
  lowerEquation_map equation swap

example : (lowerEquation (equation.map swap)).Holds arithmetic ↔
    (equation.map swap).Holds arithmetic :=
  (comparison.{0, 0, 0} Unit).satisfaction sig (Discrete.mk arithmetic) (equation.map swap)

open Isotope.Institution.Observational (Observation ssaBeh)

example : (Fiber.inputModel arithmetic Nat (entry true)).bound (0 : Fin 2) = .inl .unit := rfl
example : (Fiber.inputModel arithmetic Nat (entry true)).bound (1 : Fin 2) =
    .atom ⟨(), (4 : Nat)⟩ := rfl

private def generated := GeneratedRegion.ofGraph (P := sig) graph

example : Observation.ret (17 : Nat) (0, .atom ⟨(), (5 : Nat)⟩) 17 ∈
    ssaBeh 1 (Fiber.inputModel arithmetic Nat (entry true)) (Fiber.scope generated) :=
  (Fiber.ret_mem_eval generated arithmetic (entry true) 17 17 0 _).2
    ((lower_eval_iff graph arithmetic (entry true) 17 17 0 _).2 ⟨rfl, rfl, rfl⟩)

example : Observation.ret (17 : Nat) (0, .atom ⟨(), (5 : Nat)⟩) 18 ∉
    ssaBeh 1 (Fiber.inputModel arithmetic Nat (entry true)) (Fiber.scope generated) := by
  intro member
  have run := (Fiber.ret_mem_eval generated arithmetic (entry true) 17 18 0 _).1 member
  have state := ((lower_eval_iff graph arithmetic (entry true) 17 18 0 _).1 run).2.2
  contradiction

private def identify : sig ⟶ sig := ⟨fun | .inc | .double => .inc⟩

example : ∀ input,
    (Fiber.fiberRoom.{0, 0, 0, 0} sig inputs.length).Sat
      (Discrete.mk (Fiber.inputModel arithmetic Nat input))
      (Fiber.translateEquation (lowerEquation (equation.map identify))) :=
  (Fiber.translated_satisfaction Nat (equation.map identify) arithmetic).2 (fun _ => rfl)

example : ¬ ∀ input,
    (Fiber.fiberRoom.{0, 0, 0, 0} sig inputs.length).Sat
      (Discrete.mk (Fiber.inputModel arithmetic Nat input))
      (Fiber.translateEquation (lowerEquation equation)) := by
  intro holds
  have diff := (Fiber.translated_satisfaction Nat equation arithmetic).1 holds (entry true)
  change (5 : Nat) = 8 at diff
  cases diff

-- The same unequal diamond equation satisfies the existing room at an empty
-- state carrier, where no observation has an initial state.
example : (Fiber.fiberRoom.{0, 0, 0, 0} sig inputs.length).Sat
    (Discrete.mk (Fiber.inputModel arithmetic Empty (entry true)))
    (Fiber.translateEquation (lowerEquation equation)) :=
  Fiber.empty_state_satisfies (σ := Empty) (lowerEquation equation) arithmetic (entry true)

end Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Institution
