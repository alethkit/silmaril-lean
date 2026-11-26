module

import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Thms

namespace Silmaril.SSA.SeaOfNodes.Memory.Forwarding

open RVSDG (Origin Tuple)

private abbrev args : List ValueSort := [.address, .address, .word, .word]

private def firstAddress {past : List (List ValueSort)} : Origin args past .address :=
  .arg .head

private def secondAddress {past : List (List ValueSort)} : Origin args past .address :=
  .arg (.tail .head)

private def firstWord {past : List (List ValueSort)} : Origin args past .word :=
  .arg (.tail (.tail .head))

private def secondWord {past : List (List ValueSort)} : Origin args past .word :=
  .arg (.tail (.tail (.tail .head)))

-- The intervening Load preserves memory version 1. The selected Load feeds
-- both a later Store and the Return, with one more Load in the suffix.
private def before : Graph args :=
  .store (.latest 0) firstAddress firstWord
    (.load (.latest 1) firstAddress
      (.load (.latest 1) firstAddress
        (.store (.latest 1) secondAddress (.output (0 : Fin 2) .head)
          (.load (.latest 2) secondAddress
            (.ret (.latest 2) (.output (1 : Fin 3) .head))))))

private def after : Graph args :=
  .store (.latest 0) firstAddress firstWord
    (.load (.latest 1) firstAddress
      (.store (.latest 1) secondAddress firstWord
        (.load (.latest 2) secondAddress (.ret (.latest 2) firstWord))))

private theorem accepted : rewrite before ⟨1, 2⟩ = some after := rfl

private def x : Address 2 := 0
private def y : Address 2 := 1
private def initial : Heap 2 := fun _ => 7
private def input : Tuple (Val 2) args := .cons x (.cons y (.cons (11 : Word) (.cons (33 : Word) .nil)))
private def final : Heap 2 := (initial.write x 11).write y 11

example : after.denote input initial = (11, final) := rfl

example : after.Returns input initial 11 final :=
  (rewrite_returns_iff accepted input initial 11 final).mpr
    ((before.returns_iff_denote input initial 11 final).mpr rfl)

-- The load has the same address, but it observes version 2 from the overwrite.
private def overwrite : Graph args :=
  .store (.latest 0) firstAddress firstWord
    (.store (.latest 1) firstAddress secondWord
      (.load (.latest 2) firstAddress (.ret (.latest 2) (.output (0 : Fin 1) .head))))

private def forwardedOverwrite : Graph args :=
  .store (.latest 0) firstAddress firstWord
    (.store (.latest 1) firstAddress secondWord (.ret (.latest 2) secondWord))

example : rewrite overwrite ⟨1, 2⟩ = none := rfl
example : rewrite overwrite ⟨2, 2⟩ = some forwardedOverwrite := rfl
example : forwardedOverwrite.denote input initial = (33, (initial.write x 11).write x 33) := rfl

-- Distinct argument wires can alias at runtime. Argument identity alone is checked.
private def otherPort : Graph args :=
  .store (.latest 0) firstAddress firstWord
    (.load (.latest 1) secondAddress (.ret (.latest 1) (.output (0 : Fin 1) .head)))

example : rewrite otherPort ⟨1, 1⟩ = none := rfl

end Silmaril.SSA.SeaOfNodes.Memory.Forwarding
