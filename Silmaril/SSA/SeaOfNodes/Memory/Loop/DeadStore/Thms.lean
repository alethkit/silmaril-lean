module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.DeadStore.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.DeadStore.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.DeadStore

open RVSDG (Tuple)
open Memory.DeadStore (Candidate)
open Memory.Forwarding.Disjoint (Certificate)

variable {args : List ValueSort} {cells : Nat}
variable {graph rewritten : Graph args} {candidate : Candidate} {facts : Certificate args}

theorem rewrite_eq_some_iff (input : Tuple (Val cells) args) :
    rewrite graph candidate facts input = some rewritten ↔
      rewriteWith graph candidate facts = some rewritten ∧ facts.Valid input := by
  simp only [rewrite, ← facts.check_iff_valid input]
  split <;> simp_all

/-- The whole activation exports the same test word and heap. -/
theorem rewriteWith_body_denote (success : rewriteWith graph candidate facts = some rewritten)
    (input : Tuple (Val cells) args) (valid : facts.Valid input) (heap : Heap cells) :
    rewritten.body.denote input heap = graph.body.denote input heap :=
  Proofs.rewrite_body_denote success input valid heap

/-- Both the exit result and the heap carried on feedback are preserved. -/
theorem rewriteWith_step (success : rewriteWith graph candidate facts = some rewritten)
    (input : Tuple (Val cells) args) (valid : facts.Valid input) (heap : Heap cells) :
    rewritten.step input heap = graph.step input heap :=
  Proofs.rewrite_step success input valid heap

theorem rewriteWith_evalAfter (success : rewriteWith graph candidate facts = some rewritten)
    (input : Tuple (Val cells) args) (valid : facts.Valid input) (initial : Heap cells) (count : Nat) :
    rewritten.evalAfter input initial count = graph.evalAfter input initial count :=
  Proofs.rewrite_evalAfter success input valid initial count

theorem rewriteWith_returnsAfter_iff (success : rewriteWith graph candidate facts = some rewritten)
    (input : Tuple (Val cells) args) (valid : facts.Valid input)
    (initial : Heap cells) (count : Nat) (word : Word) (final : Heap cells) :
    rewritten.ReturnsAfter input initial count word final ↔ graph.ReturnsAfter input initial count word final := by
  rw [rewritten.returnsAfter_iff_evalAfter, graph.returnsAfter_iff_evalAfter,
    rewriteWith_evalAfter success input valid]

/-- A finite return preserves the word and entire final heap in both directions. -/
theorem rewriteWith_returns_iff (success : rewriteWith graph candidate facts = some rewritten)
    (input : Tuple (Val cells) args) (valid : facts.Valid input) (initial : Heap cells)
    (word : Word) (final : Heap cells) :
    rewritten.Returns input initial word final ↔ graph.Returns input initial word final :=
  exists_congr (fun count => rewriteWith_returnsAfter_iff success input valid initial count word final)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.DeadStore
