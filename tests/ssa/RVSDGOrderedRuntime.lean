module

import Silmaril.SSA.RVSDG.OrderedRuntime.Thms

namespace Silmaril.SSA.RVSDG.OrderedRuntime.Tests

open Silmaril.RuntimeWires

private inductive Effect where
  | add
  | double

private abbrev poly : EffectfulPolygraph where
  Obj := Unit
  pure := ⟨Unit, fun _ => [()], fun _ => [()]⟩
  effect := ⟨Effect, fun _ => [()], fun _ => [()]⟩

private abbrev word : List poly.Obj := [()]
private abbrev boundary := ports poly word
private abbrev sigs := [boundary, boundary, boundary]

private def pureStep : Instruction poly word word := .pure ()
private def effectStep (e : Effect) : Instruction poly word word := .effect e

private def term (first second : Effect) : Term (Opcode poly) boundary [] sigs boundary :=
  .bind (node .entry pureStep) (fun i => i.elim0)
    (.bind (node (.vertex [] word) (effectStep first)) (fun i => i.elim0)
      (.bind (node (.vertex [boundary] word) (effectStep second)) (fun i => i.elim0)
        (.ret (route _ (Frontier.vertex (G := poly) (root := word) [boundary, boundary] word).origin))))

private def witness (first second : Effect) : Chain poly word word .entry (term first second) :=
  .bind .entry pureStep (.bind (.vertex [] word) (effectStep first)
    (.bind (.vertex [boundary] word) (effectStep second) (.ret (.vertex [boundary, boundary] word))))

private def graph (first second : Effect) : Graph (Opcode poly) boundary [] sigs boundary :=
  (term first second).toGraph

private def admitted (first second : Effect) : Chain poly word word .entry (graph first second).toTerm := by
  change Chain poly word word .entry (term first second).toGraph.toTerm
  rw [Term.toTerm_toGraph]
  exact witness first second

private def model : Model poly where
  value _ := Nat
  runtime := Nat
  pure _ | .cons x .nil => .cons (Nat.succ x) .nil
  effect
    | .add, .cons rt data@(.cons x .nil) => .cons ((show Nat from rt) + (show Nat from x)) data
    | .double, .cons rt data => .cons (2 * (show Nat from rt)) data

private def tuple (rt x : Nat) : Tuple model.Val boundary := .cons rt (.cons x .nil)

example : denoteFunctions model (graph .add .double) (admitted .add .double) (tuple 3 1) =
    tuple 10 2 := (denoteFunctions_run model _ _ _).trans rfl

example : denoteFunctions model (graph .double .add) (admitted .double .add) (tuple 3 1) =
    tuple 8 2 := (denoteFunctions_run model _ _ _).trans rfl

example : denoteFunctions model (graph .add .double) (admitted .add .double) (tuple 3 1) ≠
    denoteFunctions model (graph .double .add) (admitted .double .add) (tuple 3 1) := by
  rw [denoteFunctions_run, denoteFunctions_run]
  intro h
  have neq : (10 : Nat) ≠ 8 := by decide
  exact neq (congrArg (fun xs => xs.get .head) h)

end Silmaril.SSA.RVSDG.OrderedRuntime.Tests
