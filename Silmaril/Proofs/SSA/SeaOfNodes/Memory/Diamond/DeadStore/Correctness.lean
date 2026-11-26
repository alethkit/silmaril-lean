module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Proofs

open RVSDG (Tuple)
open SeaOfNodes.Diamond (Projection Slot)

variable {args : List ValueSort} {cells : Nat}
variable {source : Prefixed args} {rewritten : Graph args} {candidate : Candidate args}

theorem prepend_denote (store : PrefixStore args) (arm : Memory.Graph args)
    (input : Tuple (Val cells) args) (initial : Heap cells) :
    (store.prepend arm).denote input initial = arm.denote input (store.table.denote input initial).2 :=
  Memory.DeadStore.reindexMemory_denote arm 1 input PUnit.unit _

theorem returns_iff_denote (source : Prefixed args) (guard : Bool) (input : Tuple (Val cells) args)
    (initial : Heap cells) (word : Word) (final : Heap cells) :
    source.Returns guard input initial word final ↔ source.denote guard input initial = (word, final) := by
  simp only [Prefixed.Returns, Memory.Graph.returns_iff_denote, Graph.returns_iff_denote, Prefixed.denote]
  constructor
  · rintro ⟨_, _, entry, taken⟩
    rw [entry]
    exact taken
  · intro observed
    exact ⟨_, _, rfl, observed⟩

private theorem rewrite_result (input : Tuple (Val cells) args)
    (success : rewrite source candidate input = some rewritten) :
    rewritten.suffix = source.diamond.suffix ∧
      ∀ arrival, rewriteSlot source candidate input arrival =
        some (rewritten.arm (source.diamond.merge.predecessor arrival)) := by
  obtain ⟨first, firstAccepted, afterFirst⟩ := Option.bind_eq_some_iff.mp success
  obtain ⟨second, secondAccepted, returned⟩ := Option.bind_eq_some_iff.mp afterFirst
  cases Option.some.inj returned
  refine ⟨rfl, fun arrival => ?_⟩
  change rewriteSlot source candidate input arrival = some (match
      source.diamond.merge.slot (source.diamond.merge.predecessor arrival) with
    | .first => first
    | .second => second)
  rw [source.diamond.merge.slot_predecessor]
  cases arrival
  · exact firstAccepted
  · exact secondAccepted

theorem rewrite_occurrence (input : Tuple (Val cells) args)
    (success : rewrite source candidate input = some rewritten) (arrival : Slot) :
    rewriteSlot source candidate input arrival = some (rewritten.arm (source.diamond.merge.predecessor arrival)) :=
  (rewrite_result input success).2 arrival

private theorem rewriteSlot_denote (input : Tuple (Val cells) args) (arrival : Slot)
    {arm : Memory.Graph args} (accepted : rewriteSlot source candidate input arrival = some arm)
    (initial : Heap cells) :
    arm.denote input initial =
      (source.diamond.arm (source.diamond.merge.predecessor arrival)).denote input
        (source.store.table.denote input initial).2 := by
  obtain ⟨checked, valid⟩ := (Memory.DeadStore.rewrite_eq_some_iff input).mp accepted
  exact (Memory.DeadStore.rewriteWith_denote checked input valid initial).trans
    (prepend_denote source.store _ input initial)

theorem rewrite_denote (input : Tuple (Val cells) args)
    (success : rewrite source candidate input = some rewritten) (guard : Bool) (initial : Heap cells) :
    rewritten.denote guard input initial = source.denote guard input initial := by
  obtain ⟨suffix, arms⟩ := rewrite_result input success
  let arrival := source.diamond.merge.slot (Projection.ofBool guard)
  have same := rewriteSlot_denote input arrival (arms arrival) initial
  dsimp only [arrival] at same
  rw [source.diamond.merge.predecessor_slot] at same
  simp only [Graph.denote, Prefixed.denote, suffix, same]

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Proofs
