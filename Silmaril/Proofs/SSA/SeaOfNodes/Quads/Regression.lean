module

import Silmaril.SSA.SeaOfNodes.Quads.Thms

namespace Silmaril.SSA.SeaOfNodes.Quads

open RVSDG (Port Tuple)
open Diamond (ValueSort Signature Model Val dataPorts)

private abbrev word : ValueSort Unit := .data ()

private inductive Arithmetic : Signature Unit where
  | add : Arithmetic [word, word] word

private def model : Model Arithmetic where
  value _ := Int
  run
    | .add, .cons x (.cons y .nil) => Int.add x y

private abbrev bank := dataPorts [word, word]
private def x : Port bank (.value word) := .head
private def y : Port bank (.value word) := .tail .head

private def code : Code Arithmetic [word, word] word :=
  let operands : Tuple (Port bank) bank := .cons x (.cons y .nil)
  .assign x .add operands
    (.assign y .add operands
      (.assign x .add operands
        (.assign y .add operands (.ret y))))

private def first : Fin code.producers.length := ⟨0, by decide⟩
private def redefine : Fin code.producers.length := ⟨2, by decide⟩
private def later : Fin code.producers.length := ⟨3, by decide⟩

-- The first self-read uses the entry value of x.
example : (code.lower.nodes first).inputs.get (by exact x) = .arg x := rfl

-- Writing y leaves x's current definition available for the redefinition of x.
example : ((code.lower.nodes redefine).inputs.get (by exact x)).producer = some 0 := rfl
example : ((code.lower.nodes redefine).inputs.get (by exact y)).producer = some 1 := rfl

-- The next instruction sees the new x and the previous y, before overwriting y.
example : ((code.lower.nodes later).inputs.get (by exact x)).producer = some 2 := rfl
example : ((code.lower.nodes later).inputs.get (by exact y)).producer = some 1 := rfl
example : (code.lower.results.get .head).producer = some 3 := rfl

private def input : Tuple (Val model.value) bank := .cons (3 : Int) (.cons (5 : Int) .nil)

example : code.eval model input = (34 : Int) := rfl
example : (code.lower.run model.toRVSDG input).get .head = (34 : Int) := rfl

end Silmaril.SSA.SeaOfNodes.Quads
