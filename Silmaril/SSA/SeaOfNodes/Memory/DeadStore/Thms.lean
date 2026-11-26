module

public import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.DeadStore.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.DeadStore

open RVSDG (Locals Tuple)
open Memory.Forwarding.Disjoint (Certificate)

variable {args : List ValueSort} {cells : Nat}
variable {graph rewritten : Graph args} {candidate : Candidate} {facts : Certificate args}

/-- Renumbering the live chain preserves the returned word and heap. -/
theorem reindexMemory_denote {past : List (List ValueSort)} {version : Nat}
    (body : Body args past version) (live : Nat) (input : Tuple (Val cells) args)
    (locals : Locals (Val cells) past) (heap : Heap cells) :
    (reindexMemory body live).denote input locals heap = body.denote input locals heap :=
  Proofs.reindexMemory_denote body live input locals heap

theorem rewrite_eq_some_iff (input : Tuple (Val cells) args) :
    rewrite graph candidate facts input = some rewritten ↔
      rewriteWith graph candidate facts = some rewritten ∧ facts.Valid input := by
  simp only [rewrite, ← facts.check_iff_valid input]
  split <;> simp_all

/-- An accepted elimination preserves both observations for every heap
and input satisfying the reader certificate. -/
theorem rewriteWith_denote (success : rewriteWith graph candidate facts = some rewritten)
    (input : Tuple (Val cells) args) (valid : facts.Valid input) (heap : Heap cells) :
    rewritten.denote input heap = graph.denote input heap :=
  Proofs.rewriteWith_denote success input valid heap

theorem rewriteWith_returns_iff (success : rewriteWith graph candidate facts = some rewritten)
    (input : Tuple (Val cells) args) (valid : facts.Valid input)
    (initial : Heap cells) (word : Word) (final : Heap cells) :
    rewritten.Returns input initial word final ↔ graph.Returns input initial word final := by
  rw [rewritten.returns_iff_denote, graph.returns_iff_denote, rewriteWith_denote success input valid]

/-- A checked invocation preserves and reflects the explicit memory-edge observation. -/
theorem rewrite_returns_iff (input : Tuple (Val cells) args)
    (success : rewrite graph candidate facts input = some rewritten)
    (initial : Heap cells) (word : Word) (final : Heap cells) :
    rewritten.Returns input initial word final ↔ graph.Returns input initial word final := by
  obtain ⟨accepted, valid⟩ := (rewrite_eq_some_iff input).mp success
  exact rewriteWith_returns_iff accepted input valid initial word final

end Silmaril.SSA.SeaOfNodes.Memory.DeadStore
