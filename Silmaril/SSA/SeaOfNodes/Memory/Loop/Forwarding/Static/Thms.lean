module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Static.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Forwarding.Static.Correctness

/-! # One static rewrite preserves every admissible invocation -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Static

open RVSDG (Tuple)

variable {args : List ValueSort} {cells : Nat}
variable {graph : Graph args} {candidate : Memory.Forwarding.Candidate} {result : Result args}

/-- Each input satisfying the reported cell inequalities admits exactly
the graph produced by the static pass. -/
theorem rewrite_checked (success : rewrite graph candidate = some result)
    (input : Tuple (Val cells) args) (valid : result.facts.Valid input) :
    Memory.Loop.Forwarding.rewrite graph candidate result.facts input = some result.graph :=
  Proofs.rewrite_checked success input valid

/-- Preserve the activation's scalar export and entire heap at every
latched heap in an admissible invocation. -/
theorem rewrite_body_denote (success : rewrite graph candidate = some result)
    (input : Tuple (Val cells) args) (valid : result.facts.Valid input) (heap : Heap cells) :
    result.graph.body.denote input heap = graph.body.denote input heap :=
  Memory.Loop.Forwarding.rewrite_body_denote (rewrite_checked success input valid) heap

theorem rewrite_step (success : rewrite graph candidate = some result)
    (input : Tuple (Val cells) args) (valid : result.facts.Valid input) (heap : Heap cells) :
    result.graph.step input heap = graph.step input heap :=
  Memory.Loop.Forwarding.rewrite_step (rewrite_checked success input valid) heap

theorem rewrite_evalAfter (success : rewrite graph candidate = some result)
    (input : Tuple (Val cells) args) (valid : result.facts.Valid input) (initial : Heap cells) (count : Nat) :
    result.graph.evalAfter input initial count = graph.evalAfter input initial count :=
  Memory.Loop.Forwarding.rewrite_evalAfter (rewrite_checked success input valid) initial count

theorem rewrite_denote (success : rewrite graph candidate = some result)
    (input : Tuple (Val cells) args) (valid : result.facts.Valid input) (initial : Heap cells) :
    result.graph.denote input initial = graph.denote input initial :=
  Memory.Loop.Forwarding.rewrite_denote (rewrite_checked success input valid) initial

theorem rewrite_returnsAfter_iff (success : rewrite graph candidate = some result)
    (input : Tuple (Val cells) args) (valid : result.facts.Valid input)
    (initial : Heap cells) (count : Nat) (word : Word) (final : Heap cells) :
    result.graph.ReturnsAfter input initial count word final ↔ graph.ReturnsAfter input initial count word final :=
  Memory.Loop.Forwarding.rewrite_returnsAfter_iff (rewrite_checked success input valid) initial count word final

theorem rewrite_returns_iff (success : rewrite graph candidate = some result)
    (input : Tuple (Val cells) args) (valid : result.facts.Valid input)
    (initial : Heap cells) (word : Word) (final : Heap cells) :
    result.graph.Returns input initial word final ↔ graph.Returns input initial word final :=
  Memory.Loop.Forwarding.rewrite_returns_iff (rewrite_checked success input valid) initial word final

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Static
