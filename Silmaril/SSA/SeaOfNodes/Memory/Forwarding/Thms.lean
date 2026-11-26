module

public import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Forwarding.Correctness

/-! # Checked load forwarding preserves the word and final heap -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Forwarding

open RVSDG (Tuple)

variable {args : List ValueSort} {cells : Nat}
variable {graph rewritten : Graph args} {candidate : Candidate}

/-- The rewritten graph has the same complete denotation for every input. -/
theorem rewrite_denote (success : rewrite graph candidate = some rewritten)
    (input : Tuple (Val cells) args) (heap : Heap cells) :
    rewritten.denote input heap = graph.denote input heap :=
  Proofs.rewrite_denote success input heap

/-- Accepted forwarding preserves and reflects the source snapshot observation. -/
theorem rewrite_returns_iff (success : rewrite graph candidate = some rewritten)
    (input : Tuple (Val cells) args) (heap : Heap cells) (word : Word) (final : Heap cells) :
    rewritten.Returns input heap word final ↔ graph.Returns input heap word final := by
  rw [rewritten.returns_iff_denote, graph.returns_iff_denote, rewrite_denote success]

end Silmaril.SSA.SeaOfNodes.Memory.Forwarding
