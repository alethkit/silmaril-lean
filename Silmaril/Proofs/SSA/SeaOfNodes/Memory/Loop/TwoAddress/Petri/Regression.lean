module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Petri.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Activation.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Petri.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Activation.Defs

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Petri

open CategoryTheory
open RVSDG (Port Tuple)
open Memory.Diamond.Institution renaming Signature → EntrySignature
open Loop.Institution.Lowering.Backends.Activation (bindAddress)
open RVSDG.NestedTheta.Petri (Finishes)
open RVSDG.OrderedRuntime.Structured (Threaded)

private abbrev args : List ValueSort := [.address, .address, .address, .word]

private def copyTo : Port (activationArgs args) .address :=
  .tail (.tail (.tail (.tail .head)))

private def zero : Port (activationArgs args) .word :=
  .tail (.tail (.tail (.tail (.tail .head))))

-- Save the first cell for the tail test, clear it, then read the second
-- cell from the new heap. Copy that second load to a third captured cell.
private def body : Memory.Graph (activationArgs args) :=
  .load (.latest 0) (.arg .head)
    (.store (.latest 0) (.arg .head) (.arg zero)
      (.load (.latest 1) (.arg (.tail .head))
        (.store (.latest 1) (.arg copyTo) (.output 0 .head)
          (.ret (.latest 2) (.output 1 .head)))))

private abbrev captures : EntrySignature := ⟨args⟩
private abbrev banks : EntrySignature := ⟨activationArgs args⟩

-- Compose the two bindings into the same source bank.
private def swap : banks ⟶ banks :=
  bindAddress (.tail .head) (bindAddress .head (⟨fun p => .tail (.tail p)⟩ : captures ⟶ banks))

private def graph : Graph args :=
  ⟨⟨body, rfl, zero⟩, .head, .tail .head,
    EntrySignature.Hom.port swap .head, EntrySignature.Hom.port swap (.tail .head)⟩

private def input (second : Address 4) : Tuple (Val 4) args :=
  .cons (0 : Address 4) (.cons second (.cons (2 : Address 4) (.cons (0 : Word) .nil)))

private def initial : Heap 4 :=
  fun cell => if cell = 0 then 7 else if cell = 1 then 5 else if cell = 2 then 99 else 42

private def afterFirst : Heap 4 := (initial.write 0 0).write 2 5
private def afterSecond : Heap 4 := (afterFirst.write 1 0).write 2 0
private def final : Heap 4 := (afterSecond.write 0 0).write 2 0
private def aliasFirst : Heap 4 := (initial.write 0 0).write 2 0
private def aliased : Heap 4 := (aliasFirst.write 0 0).write 2 0

-- Sequential copies would collapse the lanes. The two exact packets
-- show the pair swapped simultaneously at each feedback.
example : Finishes (thetaRuntime 4) (lowerActivation graph) (encodeHeader ⟨0, 1, initial⟩ (input 1))
    (.cons ⟨1⟩ (encodeHeader ⟨1, 0, afterFirst⟩ (input 1))) :=
  (lowerActivation_finishes_iff graph (input 1) ⟨0, 1, initial⟩ _).mpr rfl

example : (lowerActivation graph).run (thetaRuntime 4) 0 (encodeHeader ⟨1, 0, afterFirst⟩ (input 1)) =
    some (.cons ⟨1⟩ (encodeHeader ⟨0, 1, afterSecond⟩ (input 1))) := by
  rw [lowerActivation_run]
  rfl

-- Each whole-net witness starts at a single entry marking with its own
-- input and observes all cells. Coincident inputs still execute the body.
example : Finishes (thetaRuntime 4) (lower graph) (encodeInput initial (input 1))
    (encodeResult 0 final) :=
  (lower_finishes_iff graph (input 1) initial 0 final).mpr ⟨2, rfl⟩

example : Finishes (thetaRuntime 4) (lower graph) (encodeInput initial (input 0))
    (encodeResult 0 aliased) :=
  (lower_finishes_iff graph (input 0) initial 0 aliased).mpr ⟨1, rfl⟩

private def summarize (result : Option (Tuple (WireVal 4) (Threaded wordPorts))) :
    Option (Word × Word × Word × Word × Word) :=
  result.map fun
    | .cons word (.cons heap .nil) => (word, heap 0, heap 1, heap 2, heap 3)

-- The numbered graph needs three activations for two backedges.
#guard ((lower graph).run (thetaRuntime 4) 2 (encodeInput initial (input 1))).isNone
#guard summarize ((lower graph).run (thetaRuntime 4) 3 (encodeInput initial (input 1))) ==
  some (0, 0, 0, 0, 42)
#guard ((lower graph).run (thetaRuntime 4) 1 (encodeInput initial (input 0))).isNone
#guard summarize ((lower graph).run (thetaRuntime 4) 2 (encodeInput initial (input 0))) ==
  some (0, 0, 5, 0, 42)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Petri
