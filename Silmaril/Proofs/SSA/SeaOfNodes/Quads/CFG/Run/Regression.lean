module

import Silmaril.SSA.SeaOfNodes.Quads.CFG.Run.Thms

namespace Silmaril.SSA.SeaOfNodes.Quads.CFG

open RVSDG (Port Tuple)
open Diamond (ValueSort Signature Model dataPorts)

private abbrev number : ValueSort Unit := .data ()
private abbrev regs : List (ValueSort Unit) := [number, number, .predicate, .predicate, .predicate]
private abbrev ports := dataPorts regs

private inductive Arithmetic : Signature Unit where
  | add : Arithmetic [number, number] number
  | invert : Arithmetic [.predicate] .predicate

private def arithmetic : Model Arithmetic where
  value _ := Nat
  run
    | .add, .cons x (.cons y .nil) => Nat.add x y
    | .invert, .cons p .nil => ⟨!p.down⟩

private def x : Port ports (.value number) := .head
private def y : Port ports (.value number) := .tail .head
private def left : Port ports (.value .predicate) := .tail (.tail .head)
private def bypass : Port ports (.value .predicate) := .tail (.tail (.tail .head))
private def parallel : Port ports (.value .predicate) := .tail (.tail (.tail (.tail .head)))

private def add (dest a b : Port ports (.value number)) : Quad Arithmetic regs :=
  ⟨_, _, dest, .add, .cons a (.cons b .nil)⟩

private def cfg : Graph Arithmetic regs 5 :=
  let start : Graph Arithmetic regs 1 := .entry [⟨_, _, left, .invert, .cons left .nil⟩]
  let arm := start.snoc ⟨0, []⟩ [add x x y]
  let join := arm.snoc ⟨0, [1]⟩ [add y y x]
  let shared := join.snoc ⟨1, [2, 2]⟩ [add x x y]
  shared.snoc ⟨3, []⟩ []

private def e01 : Edge cfg 0 := .earlier (.earlier (.earlier (.latest 0)))
private def e02 : Edge cfg 0 := .earlier (.earlier (.latest 0))
private def e12 : Edge cfg 1 := .earlier (.earlier (.latest 1))
private def e13 : Edge cfg 1 := .earlier (.latest 0)
private def e23true : Edge cfg 2 := .earlier (.latest 1)
private def e23false : Edge cfg 2 := .earlier (.latest 2)
private def e34 : Edge cfg 3 := .latest 0

private def exitAt : (i : Fin 5) → Terminator cfg i number :=
  Fin.cases (.branch left e01 e02 (fun h => by cases congrArg Edge.target h))
    (Fin.cases (.branch bypass e13 e12 (fun h => by cases congrArg Edge.target h))
      (Fin.cases (.branch parallel e23true e23false (fun h => by cases congrArg Edge.slot h))
        (Fin.cases (.jump e34) (fun _ => .ret x))))

private theorem onlySlot (slot : Fin 1) : slot = 0 :=
  Fin.eq_of_val_eq (by have := slot.isLt; omega)

private def program : Program cfg number where
  terminator := exitAt
  covers := by
    intro source edge
    cases edge with
    | latest slot =>
      have eq : slot = 0 := onlySlot slot
      subst slot
      exact .head _
    | earlier edge =>
      cases edge with
      | latest slot =>
        cases slot using Fin.cases with
        | zero => exact .head _
        | succ slot =>
          cases slot using Fin.cases with
          | zero => exact .head _
          | succ slot =>
            have eq : slot = 0 := onlySlot slot
            subst slot
            exact .tail _ (.head _)
      | earlier edge =>
        cases edge with
        | latest slot =>
          cases slot using Fin.cases with
          | zero => exact .tail _ (.head _)
          | succ slot =>
            have eq : slot = 0 := onlySlot slot
            subst slot
            exact .tail _ (.head _)
        | earlier edge =>
          cases edge with
          | latest slot =>
            have eq : slot = 0 := onlySlot slot
            subst slot
            exact .head _
          | earlier edge => cases edge

private def input (chooseLeft skip pick : Bool) : Bank arithmetic regs :=
  .cons (3 : Nat) (.cons (5 : Nat) (.cons ⟨chooseLeft⟩ (.cons ⟨skip⟩ (.cons ⟨pick⟩ .nil))))

private def observe (chooseLeft skip pick : Bool) : List (Nat × Nat) × Nat :=
  let outcome := program.run arithmetic (input chooseLeft skip pick)
  (outcome.path.occurrences, outcome.result)

private theorem observe_of_return (chooseLeft skip pick : Bool) (path : Path cfg 4) (result : Nat)
    (follows : program.Follows arithmetic (input chooseLeft skip pick) path)
    (returned : (exitAt 4).eval arithmetic (path.eval arithmetic (input chooseLeft skip pick)) =
      .inl result) :
    observe chooseLeft skip pick = (path.occurrences, result) := by
  have outcome := (program.run_iff arithmetic _ ⟨4, path, result⟩).mpr ⟨follows, returned⟩
  unfold observe
  rw [outcome]

-- The first predicate is read after the entry quad overwrites it.
example : observe false true false = ([(1, 0), (3, 0), (4, 0)], 13) :=
  observe_of_return _ _ _ (e34.take (e13.take (e01.take cfg.start.2))) _
    (.edge (.edge (.edge .entry e01 rfl) e13 rfl) e34 rfl) rfl

example : observe false false true = ([(1, 0), (2, 1), (3, 1), (4, 0)], 21) :=
  observe_of_return _ _ _ (e34.take (e23true.take (e12.take (e01.take cfg.start.2)))) _
    (.edge (.edge (.edge (.edge .entry e01 rfl) e12 rfl) e23true rfl) e34 rfl) rfl

-- Both case arms go to the same block and return the same value. The trace
-- still names the selected occurrence rather than only the successor.
example : observe true false true = ([(2, 0), (3, 1), (4, 0)], 11) :=
  observe_of_return _ _ _ (e34.take (e23true.take (e02.take cfg.start.2))) _
    (.edge (.edge (.edge .entry e02 rfl) e23true rfl) e34 rfl) rfl

example : observe true false false = ([(2, 0), (3, 2), (4, 0)], 11) :=
  observe_of_return _ _ _ (e34.take (e23false.take (e02.take cfg.start.2))) _
    (.edge (.edge (.edge .entry e02 rfl) e23false rfl) e34 rfl) rfl

end Silmaril.SSA.SeaOfNodes.Quads.CFG
