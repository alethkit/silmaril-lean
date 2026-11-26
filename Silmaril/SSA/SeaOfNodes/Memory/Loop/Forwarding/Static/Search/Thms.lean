module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Static.Search.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Static.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Static.Search

open RVSDG (Tuple)

variable {args : List ValueSort} {cells : Nat}
variable {graph : Graph args} {result : Static.Result args}

/-- The selected pair is accepted and every earlier pair in the search order fails. -/
theorem rewrite_eq_some_iff :
    rewrite graph = some result ↔
      ∃ earlier candidate later, candidates graph = earlier ++ candidate :: later ∧
        Static.rewrite graph candidate = some result ∧
        ∀ prior ∈ earlier, Static.rewrite graph prior = none :=
  List.findSome?_eq_some_iff

/-- Failure means the static checker rejects every enumerated pair. -/
theorem rewrite_eq_none_iff :
    rewrite graph = none ↔ ∀ candidate ∈ candidates graph, Static.rewrite graph candidate = none :=
  List.findSome?_eq_none_iff

/-- Every satisfying invocation gives the same exact-backedge evaluation. -/
theorem rewrite_evalAfter (success : rewrite graph = some result)
    (input : Tuple (Val cells) args) (valid : result.facts.Valid input)
    (initial : Heap cells) (count : Nat) :
    result.graph.evalAfter input initial count = graph.evalAfter input initial count := by
  obtain ⟨_, _, checked⟩ := List.exists_of_findSome?_eq_some success
  exact Static.rewrite_evalAfter checked input valid initial count

/-- Preserve and reflect each finite return with its complete final heap. -/
theorem rewrite_returns_iff (success : rewrite graph = some result)
    (input : Tuple (Val cells) args) (valid : result.facts.Valid input)
    (initial : Heap cells) (word : Word) (final : Heap cells) :
    result.graph.Returns input initial word final ↔ graph.Returns input initial word final := by
  obtain ⟨_, _, checked⟩ := List.exists_of_findSome?_eq_some success
  exact Static.rewrite_returns_iff checked input valid initial word final

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Static.Search
