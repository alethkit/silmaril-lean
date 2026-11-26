module

import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Static.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Thms

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding

open RVSDG (Origin Port Tuple)

private abbrev args : List ValueSort := [.address, .address, .address, .address, .word]

private def headPort : Port args .address := .head
private def tailPort : Port args .address := .tail .head
private def savedPort : Port args .address := .tail (.tail .head)
private def logPort : Port args .address := .tail (.tail (.tail .head))
private def stopPort : Port args .word := .tail (.tail (.tail (.tail .head)))

private def bodyTable (forwarded : Bool) : Memory.Graph args :=
  let oldHead : Origin args [[.word], [.word]] .word := .output (1 : Fin 2) .head
  let oldTail : Origin args [[.word], [.word]] .word := .output (0 : Fin 2) .head
  let finish : Memory.Body args [[.word], [.word]] 3 :=
    if forwarded then
      .store (.latest 3) (.arg logPort) oldHead (.ret (.latest 4) oldHead)
    else
      let loaded : Origin args [[.word], [.word], [.word]] .word := .output (0 : Fin 3) .head
      .load (.latest 3) (.arg savedPort)
        (.store (.latest 3) (.arg logPort) loaded (.ret (.latest 4) loaded))
  .load (.latest 0) (.arg headPort)
    (.load (.latest 0) (.arg tailPort)
      (.store (.latest 0) (.arg savedPort) oldHead
        (.store (.latest 1) (.arg headPort) oldTail
          (.store (.latest 2) (.arg tailPort) (.arg stopPort) finish))))

private def source : Graph args := ⟨bodyTable false, rfl, stopPort⟩
private def target : Graph args := ⟨bodyTable true, rfl, stopPort⟩
private def candidate : Memory.Forwarding.Candidate := ⟨1, 5⟩
private def certificate : Memory.Forwarding.Disjoint.Certificate args := ⟨savedPort, [headPort, tailPort]⟩

private def headCell : Address 4 := 0
private def tailCell : Address 4 := 1
private def savedCell : Address 4 := 2
private def logCell : Address 4 := 3

private def input (saved : Address 4) : Tuple (Val 4) args :=
  .cons headCell (.cons tailCell (.cons saved (.cons logCell (.cons (0 : Word) .nil))))

private def initial (head : Word) : Heap 4 := fun address =>
  if address = headCell then head else if address = tailCell then 2 else 99

private def afterRound (heap : Heap 4) (oldHead oldTail : Word) : Heap 4 :=
  (((heap.write savedCell oldHead).write headCell oldTail).write tailCell 0).write logCell oldHead

private def firstHeap : Heap 4 := afterRound (initial 1) 1 2
private def secondHeap : Heap 4 := afterRound firstHeap 2 0
private def exitHeap : Heap 4 := afterRound secondHeap 0 0

private theorem accepted : rewrite source candidate certificate (input savedCell) = some target := rfl

-- Zero backedges still perform the two shift Stores and the logging Store.
example : target.evalAfter (input savedCell) (initial 0) 0 =
    some (0, afterRound (initial 0) 0 2) := by cbv

-- The feedback heap includes the Store that takes the forwarded word.
example : target.step (input savedCell) (initial 1) = .inr firstHeap := by cbv
example : target.step (input savedCell) firstHeap = .inr secondHeap := by cbv
example : target.evalAfter (input savedCell) (initial 1) 2 = some (0, exitHeap) := by cbv

example : target.Returns (input savedCell) (initial 1) 0 exitHeap :=
  (rewrite_returns_iff accepted (initial 1) 0 exitHeap).mpr
    ⟨2, (source.returnsAfter_iff_evalAfter (input savedCell) (initial 1) 2 0 exitHeap).mpr (by cbv)⟩

-- If saved aliases head, the intervening Store overwrites the forwarded cell.
example : rewrite source candidate certificate (input headCell) = none := rfl
example : (source.body.denote (input headCell) (initial 1)).1 = 2 := by cbv

private def singleLoad : Graph args :=
  ⟨.store (.latest 0) (.arg savedPort) (.arg stopPort)
    (.load (.latest 1) (.arg savedPort) (.ret (.latest 1) (.output (0 : Fin 1) .head))), rfl, stopPort⟩

-- The native loop admission check requires at least one remaining Load.
example : rewrite singleLoad ⟨1, 1⟩ ⟨savedPort, []⟩ (input savedCell) = none := rfl

-- This equality checks the native graph and its reported writers without any valuation.
private def optimized : Static.Result args := ⟨target, certificate⟩
private theorem staticAccepted : Static.rewrite source candidate = some optimized := rfl

-- Store 2 targets the head, while the selected Load targets scratch.
example : Static.rewrite source ⟨2, 5⟩ = none := rfl

private theorem separate : optimized.facts.Valid (input savedCell) :=
  (optimized.facts.check_iff_valid (input savedCell)).mp rfl

example : optimized.graph.ReturnsAfter (input savedCell) (initial 1) 2 0 exitHeap :=
  (Static.rewrite_returnsAfter_iff staticAccepted (input savedCell) separate (initial 1) 2 0 exitHeap).mpr
    ((source.returnsAfter_iff_evalAfter (input savedCell) (initial 1) 2 0 exitHeap).mpr (by cbv))

-- Scratch may share the logging cell because that Store follows the removed Load.
private theorem sharedLog : optimized.facts.Valid (input logCell) :=
  (optimized.facts.check_iff_valid (input logCell)).mp rfl

private def sharedLogExit : Heap 4 :=
  ((((initial 0).write logCell 0).write headCell 2).write tailCell 0).write logCell 0

example : optimized.graph.evalAfter (input logCell) (initial 0) 0 = some (0, sharedLogExit) :=
  (Static.rewrite_evalAfter staticAccepted (input logCell) sharedLog (initial 0) 0).trans (by cbv)

example : optimized.facts.check (input headCell) = false := rfl

example : ¬ optimized.facts.Valid (input headCell) := by
  intro valid
  have checked := (optimized.facts.check_iff_valid (input headCell)).mpr valid
  cases checked

-- Aliasing the intervening head Store changes which word the original body reads.
example : (source.body.denote (input headCell) (initial 1)).1 = 2 ∧
    (optimized.graph.body.denote (input headCell) (initial 1)).1 = 1 := by
  constructor <;> cbv

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding
