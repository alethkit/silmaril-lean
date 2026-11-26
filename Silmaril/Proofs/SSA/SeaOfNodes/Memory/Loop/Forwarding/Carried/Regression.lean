module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Thms

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried

open RVSDG (Origin Port Tuple)

private abbrev args : List ValueSort := [.address, .address, .address, .address, .word]

private def headPort : Port args .address := .head
private def tailPort : Port args .address := .tail .head
private def refillPort : Port args .address := .tail (.tail .head)
private def logPort : Port args .address := .tail (.tail (.tail .head))
private def stopPort : Port args .word := .tail (.tail (.tail (.tail .head)))

-- Read the other two cells, log the carried head, and shift the cells
-- toward the head. The last Store and the test use the old tail word.
private def suffix (clobber : Bool) : Memory.Body args [[.word]] 0 :=
  let oldHead : Origin args [[.word], [.word], [.word]] .word := .output (2 : Fin 3) .head
  let oldTail : Origin args [[.word], [.word], [.word]] .word := .output (1 : Fin 3) .head
  let oldRefill : Origin args [[.word], [.word], [.word]] .word := .output (0 : Fin 3) .head
  let finish : Memory.Body args [[.word], [.word], [.word]] 4 :=
    if clobber then .store (.latest 4) (.arg headPort) oldHead (.ret (.latest 5) oldTail)
    else .ret (.latest 4) oldTail
  .load (.latest 0) (.arg tailPort)
    (.load (.latest 0) (.arg refillPort)
      (.store (.latest 0) (.arg logPort) oldHead
        (.store (.latest 1) (.arg tailPort) oldRefill
          (.store (.latest 2) (.arg refillPort) (.arg stopPort)
            (.store (.latest 3) (.arg headPort) oldTail finish)))))

private def source (clobber : Bool) : Loop.Graph args :=
  ⟨.load (.latest 0) (.arg headPort) (suffix clobber), rfl, stopPort⟩

private def target : Graph args := ⟨headPort, suffix false, stopPort⟩

private theorem accepted : rewrite (source false) = some target := rfl

private def headCell : Address 5 := 0
private def tailCell : Address 5 := 1
private def refillCell : Address 5 := 2
private def logCell : Address 5 := 3

private def input : Tuple (Val 5) args :=
  .cons headCell (.cons tailCell (.cons refillCell (.cons logCell (.cons (0 : Word) .nil))))

private def initial (tail : Word) : Heap 5 := fun address =>
  if address = headCell then 7 else if address = tailCell then tail
  else if address = refillCell then 2 else 99

private def updated (heap : Heap 5) (log tail head : Word) : Heap 5 :=
  (((heap.write logCell log).write tailCell tail).write refillCell 0).write headCell head

private def firstHeap : Heap 5 := updated (initial 1) 7 2 1
private def secondHeap : Heap 5 := updated firstHeap 1 0 2
private def finalHeap : Heap 5 := updated secondHeap 2 0 0

-- Entry logs the initial word 7. Feedback changes the carried word to
-- 1 and then 2. Exit logs 2 and still writes the stop word to head.
example : target.step input (target.seed input (initial 1)) = .inr ⟨1, firstHeap⟩ := by cbv
example : target.step input ⟨1, firstHeap⟩ = .inr ⟨2, secondHeap⟩ := by cbv
example : target.evalAfter input (initial 1) 2 = some (0, finalHeap) := by cbv

example : (source false).ReturnsAfter input (initial 1) 2 0 finalHeap :=
  (rewrite_returnsAfter_iff accepted input (initial 1) 2 0 finalHeap).mp (by cbv)

-- An immediate exit still logs the seeded word and performs all Stores.
example : target.evalAfter input (initial 0) 0 = some (0, updated (initial 0) 7 2 0) := by cbv
example : (source false).Returns input (initial 0) 0 (updated (initial 0) 7 2 0) :=
  (rewrite_returns_iff accepted input (initial 0) 0 (updated (initial 0) 7 2 0)).mp ⟨0, by cbv⟩

-- A later Store of the old head would make feedback carry the wrong word.
example : rewrite (source true) = none := rfl
example : ((source true).body.denote input (initial 1)).1 = 1 ∧
    ((source true).body.denote input (initial 1)).2.read headCell = 7 := by
  constructor <;> cbv

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried
