module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore

open RVSDG (Tuple)
open SeaOfNodes.Diamond (Slot)

variable {args : List ValueSort} {cells : Nat}
variable {source : Prefixed args} {rewritten : Graph args} {candidate : Candidate args}

theorem PrefixStore.prepend_denote (store : PrefixStore args) (arm : Memory.Graph args)
    (input : Tuple (Val cells) args) (initial : Heap cells) :
    (store.prepend arm).denote input initial = arm.denote input (store.table.denote input initial).2 :=
  Proofs.prepend_denote store arm input initial

theorem Prefixed.returns_iff_denote (source : Prefixed args) (guard : Bool) (input : Tuple (Val cells) args)
    (initial : Heap cells) (word : Word) (final : Heap cells) :
    source.Returns guard input initial word final ↔ source.denote guard input initial = (word, final) :=
  Proofs.returns_iff_denote source guard input initial word final

/-- Each target arm comes from its own checked Region occurrence. -/
theorem rewrite_occurrence (input : Tuple (Val cells) args)
    (success : rewrite source candidate input = some rewritten) (arrival : Slot) :
    rewriteSlot source candidate input arrival = some (rewritten.arm (source.diamond.merge.predecessor arrival)) :=
  Proofs.rewrite_occurrence input success arrival

theorem rewrite_denote (input : Tuple (Val cells) args)
    (success : rewrite source candidate input = some rewritten) (guard : Bool) (initial : Heap cells) :
    rewritten.denote guard input initial = source.denote guard input initial :=
  Proofs.rewrite_denote input success guard initial

/-- Both guard choices preserve and reflect the returned word and whole heap. -/
theorem rewrite_returns_iff (input : Tuple (Val cells) args)
    (success : rewrite source candidate input = some rewritten) (guard : Bool) (initial : Heap cells)
    (word : Word) (final : Heap cells) :
    rewritten.Returns guard input initial word final ↔ source.Returns guard input initial word final := by
  rw [rewritten.returns_iff_denote, source.returns_iff_denote, rewrite_denote input success]

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore
