module

import Silmaril.SSA.RVSDG.NestedTheta.Institution.Thms

namespace Silmaril.SSA.RVSDG.NestedTheta.Institution.Tests

open CategoryTheory Silmaril.Logic.Institution
open OrderedRuntime.Structured (Ty Values)

private abbrev dataPorts : Ports (Ty Unit) := [.value ()]
private abbrev bodyPorts : Ports (Ty Unit) := Theta.BodyResults dataPorts
private abbrev args : Ports (Ty Unit) := .control 2 :: dataPorts
private abbrev NoPure : Dialect Unit Unit := fun _ _ => Empty

private inductive SourceEffect : Dialect Unit Unit where
  | current : SourceEffect dataPorts bodyPorts
  | legacy : SourceEffect dataPorts bodyPorts

private inductive TargetEffect : Dialect Unit Unit where
  | tick : TargetEffect dataPorts bodyPorts

private abbrev source : Signature Unit := ⟨NoPure, SourceEffect⟩
private abbrev target : Signature Unit := ⟨NoPure, TargetEffect⟩

private def migrate : source ⟶ target :=
  { pure := fun op => nomatch op
    effect := fun op => match op with
      | .current => .tick
      | .legacy => .tick }

private def body (op : SourceEffect dataPorts bodyPorts) :
    Term source.op dataPorts [] [bodyPorts] bodyPorts :=
  let node : Node source.op dataPorts [] bodyPorts :=
    ⟨dataPorts, .base (.simple (.effect op)), .cons (.arg .head) .nil, fun i => i.elim0⟩
  .bind node (fun i => i.elim0)
    (.ret (.cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil)))

private def loop (op : SourceEffect dataPorts bodyPorts) :
    Term source.op dataPorts [] [dataPorts] dataPorts :=
  .bind (thetaVertex [bodyPorts]) (fun _ => body op)
    (.ret (.cons (.output (0 : Fin 1) .head) .nil))

private abbrev choice : Node source.op args [] dataPorts :=
  ⟨args, .base (.gamma 0), .cons (.arg .head) (.cons (.arg (.tail .head)) .nil),
    Fin.cases [dataPorts] (fun _ => [])⟩

private def program (op : SourceEffect dataPorts bodyPorts) :
    Term source.op args [] [dataPorts] dataPorts :=
  .bind choice
    (Fin.cases (motive := fun i => Term source.op dataPorts [] (choice.childSigs i) dataPorts)
      (loop op) (fun _ => .ret (.cons (.arg .head) .nil)))
    (.ret (.cons (.output (0 : Fin 1) .head) .nil))

private def equation : Equation source :=
  ⟨args, dataPorts, [dataPorts], [dataPorts],
    (program .current).toGraph, (program .legacy).toGraph⟩

private abbrev value : Unit → Type := fun _ => Nat

private def tick (increment : Nat) (input : Tuple (Values value) dataPorts) :
    StateM Nat (Tuple (Values value) bodyPorts) :=
  match input with
  | .cons n .nil => StateT.mk fun store =>
    let tag : Fin 2 := if (show Nat from n) = 0 then 1 else 0
    (.cons ⟨tag⟩ (.cons (1 : Nat) .nil), store + increment)

private def migratedModel : Model target Nat where
  value := value
  runPure op := nomatch op
  effect
    | .tick => tick 1

private def differentStoreModel : Model source Nat where
  value := value
  runPure op := nomatch op
  effect
    | .current => tick 1
    | .legacy => tick 10

private def data (n : Nat) : Tuple (Values value) dataPorts := .cons n .nil
private def selected : Tuple (Values value) args := .cons ⟨(0 : Fin 2)⟩ (data 0)

private abbrev dialectInst : Inst.{1, 0, 0, 1, 1} := inst Unit Nat

example : SourceEffect.current ≠ SourceEffect.legacy := by
  intro h
  cases h

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem mappedGraphs : (equation.map migrate).lhs = (equation.map migrate).rhs := by
  simp only [equation, Equation.map, mapGraph, Term.toTerm_toGraph]
  congr 1
  simp only [program, mapTerm]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

-- Both source operations migrate to tick, so the translated numbered graphs coincide.
example : (dialectInst.I.obj source).Sat
    ((dialectInst.I.map migrate).mod.obj (Discrete.mk migratedModel)) equation := by
  apply ((dialectInst.I.map migrate).sat (Discrete.mk migratedModel) equation).mp
  change (equation.map migrate).Holds migratedModel
  intro input store
  rw [mappedGraphs]

private def result (tag : Fin 2) : Tuple (Values value) bodyPorts := .cons ⟨tag⟩ (data 1)

private theorem currentFinite :
    OrderedState.exec differentStoreModel (program .current) selected PUnit.unit 0 (data 1, 2) := by
  refine ⟨(data 1, 2), ⟨(data 1, 2), ?_, rfl⟩, rfl⟩
  refine Theta.Iterate.again (next := (data 1, 1)) ?_ (Theta.Iterate.stop ?_)
  · exact ⟨(result 1, 1), rfl, rfl⟩
  · exact ⟨(result 0, 2), rfl, rfl⟩

private theorem legacyFinite :
    OrderedState.exec differentStoreModel (program .legacy) selected PUnit.unit 0 (data 1, 20) := by
  refine ⟨(data 1, 20), ⟨(data 1, 20), ?_, rfl⟩, rfl⟩
  refine Theta.Iterate.again (next := (data 1, 10)) ?_ (Theta.Iterate.stop ?_)
  · exact ⟨(result 1, 10), rfl, rfl⟩
  · exact ⟨(result 0, 20), rfl, rfl⟩

-- On the selected γ arm θ takes one restart. The two payloads agree,
-- but the two final stores differ in this source model.
example : ¬ equation.Holds differentStoreModel := by
  intro holds
  have left : OrderedState.observe differentStoreModel equation.lhs selected 0 =
      Part.some (data 1, 2) :=
    (OrderedState.observe_eq_some differentStoreModel _ _ _ _).mpr
      (by simpa only [equation, Term.toTerm_toGraph] using currentFinite)
  have right : OrderedState.observe differentStoreModel equation.rhs selected 0 =
      Part.some (data 1, 20) :=
    (OrderedState.observe_eq_some differentStoreModel _ _ _ _).mpr
      (by simpa only [equation, Term.toTerm_toGraph] using legacyFinite)
  have same := holds selected 0
  rw [left, right] at same
  exact (by decide : (2 : Nat) ≠ 20) (congrArg Prod.snd (Part.some_injective same))

end Silmaril.SSA.RVSDG.NestedTheta.Institution.Tests
