module

import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.Thms

meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Defs

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite

open RVSDG (Origin Port Tuple)
open Quads.CFG (Predecessors)
open Silmaril.MLIR.MemRef (Buffer)
open SeaOfNodes.Memory.MLIR.MemRef (observe)

private abbrev Args : List ValueSort := [.address, .address, .word, .word, .word]

private def headPort : Port Args .address := .head
private def sidePort : Port Args .address := .tail .head
private def entryWord : Port Args .word := .tail (.tail .head)
private def firstWord : Port Args .word := .tail (.tail (.tail .head))
private def middleWord : Port Args .word := .tail (.tail (.tail (.tail .head)))
private def loaded : Origin Args [[.word]] .word := .output 0 .head

-- The first two paths finish at the same named predecessor. Their
-- complete reaching paths and their overwrite versions differ.
private def preds : Predecessors 2 := ⟨0, [0, 1]⟩
private def reversed : Predecessors 2 := ⟨1, [0, 0]⟩

private def reverseOrder : Occurrence reversed ≃ Occurrence preds :=
  ⟨Fin.rev, Fin.rev, Fin.rev_rev, Fin.rev_rev⟩

example : List.ofFn preds.get = [0, 0, 1] := rfl
example : List.ofFn reversed.get = List.ofFn (fun i => preds.get (reverseOrder i)) := rfl

private def shared : PrefixStore Args := ⟨headPort, entryWord⟩

private def first : Memory.Graph Args :=
  .load (.latest 0) (.arg sidePort)
    (.store (.latest 0) (.arg headPort) (.arg firstWord) (.ret (.latest 1) loaded))

private def middle (reader : Port Args .address) : Memory.Graph Args :=
  .load (.latest 0) (.arg reader)
    (.store (.latest 0) (.arg sidePort) (.arg middleWord)
      (.store (.latest 1) (.arg headPort) (.arg middleWord) (.ret (.latest 2) loaded)))

private def last : Memory.Graph Args :=
  .store (.latest 0) (.arg headPort) (.arg entryWord)
    (.load (.latest 1) (.arg headPort) (.ret (.latest 1) loaded))

private def arms (middleReader : Port Args .address) (arrival : Occurrence preds) : Memory.Graph Args :=
  match arrival.val with
  | 0 => first
  | 1 => middle middleReader
  | _ => last

private def witnesses (arrival : Occurrence preds) : ArmOverwrite Args :=
  match arrival.val with
  | 0 => ⟨1, [sidePort]⟩
  | 1 => ⟨2, [sidePort]⟩
  | _ => ⟨1, []⟩

private def input : Tuple (Val 3) Args :=
  .cons (0 : Address 3) (.cons (1 : Address 3)
    (.cons (99 : Word) (.cons (11 : Word) (.cons (22 : Word) .nil))))

private def initial : Buffer 3 :=
  ⟨fun i => if i = 0 then 7 else if i = 1 then 3 else 55⟩

private def edited : Bank Args preds := #v[first, middle sidePort, last]

private theorem accepted : check preds shared (arms sidePort) witnesses input = some edited := by
  apply check_eq_some_iff.mpr
  intro arrival
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) arrival
  · rfl
  · rfl
  · rw [Fin.eq_zero j]
    rfl

example : check reversed shared (fun i => arms sidePort (reverseOrder i)) (fun i => witnesses (reverseOrder i))
    input = some (Vector.ofFn fun i => edited[(reverseOrder i).val]) :=
  check_reindex reverseOrder accepted

-- Only occurrence one observes the old cell. Occurrence zero has the
-- same predecessor identifier and still checks successfully.
example : rewriteArm shared (arms headPort 0) (witnesses 0) input = some first := rfl
example : rewriteArm shared (arms headPort 1) (witnesses 1) input = none := rfl
example : rewriteArm shared (arms headPort 2) (witnesses 2) input = some last := rfl
example : check preds shared (arms headPort) witnesses input = none :=
  check_eq_none_iff.mpr ⟨1, rfl⟩
#guard (check preds shared (arms headPort) witnesses input).isNone

#guard Memory.DeadStore.readAt (shared.prepend (arms headPort 1)) 0 input PUnit.unit initial.cell == some 99
#guard Memory.DeadStore.readAt (arms headPort 1) 0 input PUnit.unit initial.cell == some 7

private def readback (result : Word × Buffer 3) : List Nat :=
  result.1.toNat :: List.ofFn (fun i => (result.2.cell i).toNat)

private def runBank (order : Predecessors 2) (arm : Occurrence order → Memory.Graph Args)
    (candidate : Candidate Args order) : Option (List (List Nat × List Nat)) := do
  let result ← check order shared arm candidate input
  pure (List.ofFn fun i =>
    (readback (observe (shared.prepend (arm i)) input initial), readback (observe result[i.val] input initial)))

/-- info: some [[3, 11, 3, 55], [3, 22, 22, 55], [99, 99, 3, 55]] -/
#guard_msgs in
#eval (runBank preds (arms sidePort) witnesses).map (List.map Prod.snd)

#guard runBank preds (arms sidePort) witnesses ==
  some [([3, 11, 3, 55], [3, 11, 3, 55]), ([3, 22, 22, 55], [3, 22, 22, 55]), ([99, 99, 3, 55], [99, 99, 3, 55])]

#guard runBank reversed (fun i => arms sidePort (reverseOrder i)) (fun i => witnesses (reverseOrder i)) ==
  (runBank preds (arms sidePort) witnesses).map List.reverse

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite
