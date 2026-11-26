module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Forwarding.Correctness

/-! # Preservation of the activation and loop observations -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding

open RVSDG (Tuple)

variable {args : List ValueSort} {cells : Nat}
variable {graph rewritten : Graph args} {candidate : Memory.Forwarding.Candidate}
variable {certificate : Memory.Forwarding.Disjoint.Certificate args} {input : Tuple (Val cells) args}

/-- A statically accepted graph is the checked rewrite at every admissible input. -/
theorem rewriteWith_checked (success : rewriteWith graph candidate certificate = some rewritten)
    (valid : certificate.Valid input) : rewrite graph candidate certificate input = some rewritten := by
  simpa [rewrite, (certificate.check_iff_valid input).mpr valid] using success

/-- At any latched heap, the activation exports the same test word and
entire heap. -/
theorem rewrite_body_denote (success : rewrite graph candidate certificate input = some rewritten)
    (heap : Heap cells) : rewritten.body.denote input heap = graph.body.denote input heap :=
  Proofs.rewrite_body_denote success heap

/-- Each activation makes the same exit or feedback transition. -/
theorem rewrite_step (success : rewrite graph candidate certificate input = some rewritten)
    (heap : Heap cells) : rewritten.step input heap = graph.step input heap :=
  Proofs.rewrite_step success heap

/-- The exact-backedge evaluator agrees at every requested count. -/
theorem rewrite_evalAfter (success : rewrite graph candidate certificate input = some rewritten)
    (heap : Heap cells) (count : Nat) :
    rewritten.evalAfter input heap count = graph.evalAfter input heap count :=
  Proofs.rewrite_evalAfter success heap count

theorem rewrite_denote (success : rewrite graph candidate certificate input = some rewritten)
    (initial : Heap cells) : rewritten.denote input initial = graph.denote input initial :=
  Proofs.rewrite_denote success initial

theorem rewrite_returnsAfter_iff (success : rewrite graph candidate certificate input = some rewritten)
    (initial : Heap cells) (count : Nat) (word : Word) (final : Heap cells) :
    rewritten.ReturnsAfter input initial count word final ↔ graph.ReturnsAfter input initial count word final := by
  rw [rewritten.returnsAfter_iff_evalAfter, graph.returnsAfter_iff_evalAfter, rewrite_evalAfter success]

/-- The rewrite preserves and reflects finite explicit-edge observations
at the checked input and every initial heap. -/
theorem rewrite_returns_iff (success : rewrite graph candidate certificate input = some rewritten)
    (initial : Heap cells) (word : Word) (final : Heap cells) :
    rewritten.Returns input initial word final ↔ graph.Returns input initial word final := by
  rw [rewritten.returns_iff_mem_denote, graph.returns_iff_mem_denote, rewrite_denote success]

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding
