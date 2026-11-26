module

import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Disjoint.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Thms

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Disjoint

open RVSDG (Origin Port Tuple)
open SeaOfNodes.Diamond (Projection)

private abbrev args : List ValueSort := [.address, .address, .address, .word, .word]

private def xPort : Port args .address := .head
private def yPort : Port args .address := .tail .head
private def zPort : Port args .address := .tail (.tail .head)
private def eleven : Origin args [] .word := .arg (.tail (.tail (.tail .head)))
private def thirtyThree : Origin args [] .word := .arg (.tail (.tail (.tail (.tail .head))))

private def trueArm : Memory.Graph args :=
  .store (.latest 0) (.arg xPort) eleven
    (.store (.latest 1) (.arg yPort) thirtyThree
      (.ret (.latest 2) eleven))

private def falseArm : Memory.Graph args :=
  .store (.latest 0) (.arg yPort) eleven
    (.store (.latest 1) (.arg xPort) thirtyThree
      (.store (.latest 2) (.arg zPort) eleven
        (.ret (.latest 3) thirtyThree)))

private def source (first : Projection) : Graph args where
  merge := ⟨first⟩
  arm
    | .onTrue => trueArm
    | .onFalse => falseArm
  suffix := .load (.latest 0) (.arg (.tail xPort))
    (.ret (.latest 0) (.output (0 : Fin 1) .head))

private def target (first : Projection) : Graph args :=
  { source first with suffix := .ret (.latest 0) (.arg .head) }

private def normal : Candidate args := ⟨⟨1, [yPort]⟩, ⟨2, [zPort]⟩⟩
private def reversed : Candidate args := ⟨normal.second, normal.first⟩

private def x : Address 3 := 0
private def y : Address 3 := 1
private def z : Address 3 := 2
private def initial : Heap 3 := fun _ => 0

private def input (secondWriter : Address 3) : Tuple (Val 3) args :=
  .cons x (.cons y (.cons secondWriter (.cons (11 : Word) (.cons (33 : Word) .nil))))

private theorem accepted : rewrite (source .onFalse) reversed (input z) = some (target .onFalse) := rfl

example : rewrite (source .onTrue) normal (input z) = some (target .onTrue) := rfl
example : rewrite (source .onFalse) normal (input z) = none := rfl

private def finalTrue : Heap 3 := (initial.write x 11).write y 33
private def finalFalse : Heap 3 := ((initial.write y 11).write x 33).write z 11

example : (target .onFalse).Returns true (input z) initial 11 finalTrue :=
  (rewrite_returns_iff (input z) accepted true initial 11 finalTrue).mpr
    (((source .onFalse).returns_iff_denote true (input z) initial 11 finalTrue).mpr (by cbv))

example : (target .onFalse).Returns false (input z) initial 33 finalFalse :=
  (rewrite_returns_iff (input z) accepted false initial 33 finalFalse).mpr
    (((source .onFalse).returns_iff_denote false (input z) initial 33 finalFalse).mpr (by cbv))

-- The true occurrence still checks, while the false occurrence writes x through z.
example : checkSlot (source .onFalse) xPort reversed (input x) .second = true := rfl
example : checkSlot (source .onFalse) xPort reversed (input x) .first = false := rfl
example : rewrite (source .onFalse) reversed (input x) = none := rfl

example : (source .onFalse).denote false (input x) initial =
    (11, ((initial.write y 11).write x 33).write x 11) := by cbv

-- An absent fact for the false occurrence stops forwarding even at distinct cells.
example : rewrite (source .onTrue) { normal with second := ⟨2, []⟩ } (input z) = none := rfl

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Disjoint
