module

import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Thms

namespace Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint

open RVSDG (Origin Port Tuple)

private abbrev args : List ValueSort := [.address, .address, .address, .word]

private def xPort : Port args .address := .head
private def yPort : Port args .address := .tail .head
private def zPort : Port args .address := .tail (.tail .head)
private def xWire {past : List (List ValueSort)} : Origin args past .address := .arg xPort
private def yWire {past : List (List ValueSort)} : Origin args past .address := .arg yPort
private def zWire {past : List (List ValueSort)} : Origin args past .address := .arg zPort
private def newWord {past : List (List ValueSort)} : Origin args past .word :=
  .arg (.tail (.tail (.tail .head)))

private def source : Graph args :=
  .load (.latest 0) xWire
    (.store (.latest 0) xWire (.output (0 : Fin 1) .head)
      (.store (.latest 1) yWire newWord
        (.load (.latest 2) yWire
          (.load (.latest 2) xWire
            (.store (.latest 2) zWire (.output (0 : Fin 3) .head)
              (.ret (.latest 3) (.output (0 : Fin 3) .head)))))))

private def forwarded : Graph args :=
  .load (.latest 0) xWire
    (.store (.latest 0) xWire (.output (0 : Fin 1) .head)
      (.store (.latest 1) yWire newWord
        (.load (.latest 2) yWire
          (.store (.latest 2) zWire (.output (1 : Fin 2) .head)
            (.ret (.latest 3) (.output (1 : Fin 2) .head))))))

private def certificate : Certificate args := ⟨xPort, [yPort]⟩
private def candidate : Candidate := ⟨1, 4⟩

private def x : Address 3 := 0
private def y : Address 3 := 1
private def z : Address 3 := 2
private def input (written : Address 3) : Tuple (Val 3) args :=
  .cons x (.cons written (.cons z (.cons (33 : Word) .nil)))

private def initial : Heap 3 := fun address => if address = x then 11 else 0
private def final : Heap 3 := ((initial.write x 11).write y 33).write z 11

-- Store 2 stays in the memory chain while the read of x forwards Store 1's word.
private theorem accepted : rewrite source candidate certificate (input y) = some forwarded := rfl

example : forwarded.Returns (input y) initial 11 final :=
  (rewrite_returns_iff (input y) initial accepted 11 final).mpr
    ((source.returns_iff_denote (input y) initial 11 final).mpr (by cbv))

-- A valid fact about z does not cover the intervening Store on y.
example : rewrite source candidate ⟨xPort, [zPort]⟩ (input y) = none := rfl

-- The same two argument wires can denote one cell.
example : certificate.check (input x) = false := rfl
example : rewrite source candidate certificate (input x) = none := rfl

example : source.denote (input x) initial = (33, ((initial.write x 11).write x 33).write z 33) := by cbv

end Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint
