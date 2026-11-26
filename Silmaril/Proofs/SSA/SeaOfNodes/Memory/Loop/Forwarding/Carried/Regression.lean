module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Thms

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried

open RVSDG (Origin Port Tuple)
open Memory.Forwarding.Disjoint (Certificate)

private abbrev args : List ValueSort := [.address, .address, .address, .address, .word]

private def headPort : Port args .address := .head
private def tailPort : Port args .address := .tail .head
private def refillPort : Port args .address := .tail (.tail .head)
private def logPort : Port args .address := .tail (.tail (.tail .head))
private def stopPort : Port args .word := .tail (.tail (.tail (.tail .head)))

-- The tail test always uses the old tail. In the separate case the
-- last Store instead takes the old refill, and refill gets the old head.
private def suffix (separate : Bool) (writeAfter : Bool := false) : Memory.Body args [[.word]] 0 :=
  let oldHead : Origin args [[.word], [.word], [.word]] .word := .output (2 : Fin 3) .head
  let oldTail : Origin args [[.word], [.word], [.word]] .word := .output (1 : Fin 3) .head
  let oldRefill : Origin args [[.word], [.word], [.word]] .word := .output (0 : Fin 3) .head
  let refill := if separate then oldHead else .arg stopPort
  let storeWord := if separate then oldRefill else oldTail
  let finish : Memory.Body args [[.word], [.word], [.word]] 4 :=
    if writeAfter then .store (.latest 4) (.arg logPort) oldTail (.ret (.latest 5) oldTail)
    else .ret (.latest 4) oldTail
  .load (.latest 0) (.arg tailPort)
    (.load (.latest 0) (.arg refillPort)
      (.store (.latest 0) (.arg logPort) oldHead
        (.store (.latest 1) (.arg tailPort) oldRefill
          (.store (.latest 2) (.arg refillPort) refill
            (.store (.latest 3) (.arg headPort) storeWord finish)))))

private def source (separate : Bool) (writeAfter : Bool := false) : Loop.Graph args :=
  ⟨.load (.latest 0) (.arg headPort) (suffix separate writeAfter), rfl, stopPort⟩

private def target : Graph args := ⟨headPort, suffix false, stopPort, 4⟩

private theorem accepted : rewrite (source false) = some target := rfl

private def headCell : Address 5 := 0
private def tailCell : Address 5 := 1
private def refillCell : Address 5 := 2
private def logCell : Address 5 := 3

private def input : Tuple (Val 5) args :=
  .cons headCell (.cons tailCell (.cons refillCell (.cons logCell (.cons (0 : Word) .nil))))

private def initial (tail : Word) (head : Word := 7) : Heap 5 := fun address =>
  if address = headCell then head else if address = tailCell then tail
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

private def separateTarget : Graph args := ⟨headPort, suffix true, stopPort, 4⟩
private theorem separateAccepted : rewrite (source true) = some separateTarget := rfl

private def separateUpdate (heap : Heap 5) (oldHead oldRefill : Word) : Heap 5 :=
  (((heap.write logCell oldHead).write tailCell oldRefill).write refillCell oldHead).write headCell oldRefill

private def separateFirst : Heap 5 := separateUpdate (initial 1 0) 0 2
private def separateSecond : Heap 5 := separateUpdate separateFirst 2 0
private def separateFinal : Heap 5 := separateUpdate separateSecond 0 2

-- The first two guards are 1 and 2, while the backedges carry 2 and 0.
example : separateTarget.activateWithStore input (separateTarget.seed input (initial 1 0)) =
    ⟨(1, separateFirst), some 2⟩ := by cbv
example : separateTarget.activateWithStore input ⟨2, separateFirst⟩ =
    ⟨(2, separateSecond), some 0⟩ := by cbv
example : separateTarget.step input (separateTarget.seed input (initial 1 0)) =
    .inr ⟨2, separateFirst⟩ := by cbv
example : separateTarget.step input ⟨2, separateFirst⟩ = .inr ⟨0, separateSecond⟩ := by cbv

-- On exit the original Return supplies 0 and the final head cell contains 2.
example : separateTarget.evalAfter input (initial 1 0) 2 = some (0, separateFinal) := by cbv
example : separateFinal.read headCell = 2 := by cbv
example : (source true).ReturnsAfter input (initial 1 0) 2 0 separateFinal :=
  (rewrite_returnsAfter_iff separateAccepted input (initial 1 0) 2 0 separateFinal).mp (by cbv)

-- An earlier Store to head is insufficient when the last Store targets tail.
private def mismatch (destination : Port args .address := tailPort) : Loop.Graph args :=
  let oldHead : Origin args [[.word]] .word := .output (0 : Fin 1) .head
  ⟨.load (.latest 0) (.arg headPort)
    (.store (.latest 0) (.arg headPort) oldHead
      (.store (.latest 1) (.arg destination) (.arg stopPort) (.ret (.latest 2) oldHead))), rfl, stopPort⟩

example : rewrite mismatch = none := rfl
example : rewriteWith (mismatch headPort) 1 ⟨headPort, [headPort]⟩ = none := rfl

private def suffixTarget : Graph args := ⟨headPort, suffix true true, stopPort, 4⟩
private def suffixFacts : Certificate args := ⟨headPort, [logPort]⟩

private theorem suffixAccepted : rewriteChecked (source true true) 4 suffixFacts input = some suffixTarget :=
  rfl

private def suffixFirst : Heap 5 := (separateUpdate (initial 1 0) 0 2).write logCell 1
private def suffixSecond : Heap 5 := (separateUpdate suffixFirst 2 0).write logCell 2
private def suffixFinal : Heap 5 := (separateUpdate suffixSecond 0 2).write logCell 0

-- Store 5 writes the guard to log, while Store 4 still feeds head.
example : suffixTarget.step input (suffixTarget.seed input (initial 1 0)) =
    .inr ⟨2, suffixFirst⟩ := by cbv
example : suffixTarget.step input ⟨2, suffixFirst⟩ = .inr ⟨0, suffixSecond⟩ := by cbv
example : suffixTarget.evalAfter input (initial 1 0) 2 = some (0, suffixFinal) := by cbv
example : suffixFinal.read headCell = 2 ∧ suffixSecond.read logCell = 2 := by
  constructor <;> cbv

example : (source true true).Returns input (initial 1 0) 0 suffixFinal := by
  obtain ⟨accepted, valid⟩ := (rewriteChecked_eq_some_iff input).mp suffixAccepted
  exact (rewriteWith_returns_iff accepted input valid (initial 1 0) 0 suffixFinal).mp ⟨2, by cbv⟩

-- A listed writer may alias at an invocation even though its port is different.
private def aliasedInput : Tuple (Val 5) args :=
  .cons headCell (.cons tailCell (.cons refillCell (.cons headCell (.cons (0 : Word) .nil))))

example : rewriteWith (source true true) 4 ⟨headPort, []⟩ = none := rfl
example : rewriteChecked (source true true) 4 suffixFacts aliasedInput = none := rfl
example : ((source true true).body.denote aliasedInput (initial 1 0)).2.read headCell = 1 := by cbv

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried
