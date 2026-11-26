module

import Silmaril.SSA.SeaOfNodes.Quads.CFG.Thms

namespace Silmaril.SSA.SeaOfNodes.Quads.CFG

open RVSDG (Port Tuple)
open Diamond (ValueSort Signature Model dataPorts)
open Join (Block)

private abbrev number : ValueSort Unit := .data ()
private abbrev regs : List (ValueSort Unit) := [number, number, number]
private abbrev ports := dataPorts regs

private inductive Arithmetic : Signature Unit where
  | add : Arithmetic [number, number] number

private def arithmetic : Model Arithmetic where
  value _ := Nat
  run
    | .add, .cons x (.cons y .nil) => Nat.add x y

private def x : Port ports (.value number) := .head
private def y : Port ports (.value number) := .tail .head
private def stride : Port ports (.value number) := .tail (.tail .head)

private def add (dest left right : Port ports (.value number)) : Quad Arithmetic regs :=
  ⟨_, _, dest, .add, .cons left (.cons right .nil)⟩

-- Entry fans out to the left block, the first join and the shared successor.
-- The shared successor also has two distinct incoming occurrences from the first join.
private def start : Graph Arithmetic regs 1 := .entry []
private def beforeJoin : Graph Arithmetic regs 2 := start.snoc ⟨0, []⟩ [add x x stride]
private def firstPreds : Predecessors 2 := ⟨0, [1]⟩
private def firstJoin : Graph Arithmetic regs 3 := beforeJoin.snoc firstPreds [add y y x]
private def sharedPreds : Predecessors 3 := ⟨0, [2, 2]⟩
private def shared : Graph Arithmetic regs 4 := firstJoin.snoc sharedPreds [add x x y]

-- The left block reads x before overwriting it. The first join needs only x.
example : ((beforeJoin.column firstPreds 0).get x, (beforeJoin.column firstPreds 1).get x) =
    (.input, .write 1 0) := rfl
example : ((beforeJoin.header firstPreds).get x, (beforeJoin.header firstPreds).get y,
    (beforeJoin.header firstPreds).get stride) = (none, some .input, some .input) := rfl

-- The bypass gets the original x and y. Both parallel occurrences keep the
-- first join's x Φ and y write, in their original edge positions.
example : List.ofFn (fun i => ((firstJoin.column sharedPreds i).get x,
    (firstJoin.column sharedPreds i).get y)) =
    [(.input, .input), (.phi 2, .write 2 0), (.phi 2, .write 2 0)] := rfl
example : sharedPreds.get (1 : Fin 3) = sharedPreds.get (2 : Fin 3) := rfl
example : (1 : Fin 3) ≠ 2 := by decide
example : ((firstJoin.header sharedPreds).get x, (firstJoin.header sharedPreds).get y,
    (firstJoin.header sharedPreds).get stride) = (none, none, some .input) := rfl

private def bypass : Path shared 3 := .edge 0 (.earlier (.earlier .entry))
private def viaFirst : Path shared 3 := .edge 1 (.edge 0 (.earlier .entry))
private def viaSecond : Path shared 3 := .edge 2 (.edge 1 (.edge 0 .entry))

private def bank (a b c : Nat) : Bank arithmetic regs := .cons a (.cons b (.cons c .nil))
private def input := bank 3 5 2

private def readExit (path : Path shared 3) : Option (Bank arithmetic regs) := do
  let values ← path.values arithmetic input
  readBank ports (values.read (shared.versions 3))

example : [bypass, viaFirst, viaSecond].map (fun path => path.eval arithmetic input) =
    [bank 8 5 2, bank 11 8 2, bank 15 10 2] := rfl
example : [bypass, viaFirst, viaSecond].map readExit =
    [some (bank 8 5 2), some (bank 11 8 2), some (bank 15 10 2)] := rfl

-- The bypass never executes either the left block or the first join.
example : (bypass.values arithmetic input).bind (fun values => values (.write 1 0) x) = none := rfl
example : (bypass.values arithmetic input).bind (fun values => values (.phi 2) x) = none := rfl

-- No Φ value is allocated for the untouched register even on a visited join.
example : (viaSecond.values arithmetic input).bind (fun values => values (.phi 3) stride) =
    none := rfl

end Silmaril.SSA.SeaOfNodes.Quads.CFG
