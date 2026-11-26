module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Static.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Static.Proofs

open RVSDG (Tuple)

variable {args : List ValueSort} {cells : Nat}
variable {graph : Graph args} {candidate : Memory.Forwarding.Candidate} {result : Result args}

theorem rewrite_checked (success : rewrite graph candidate = some result)
    (input : Tuple (Val cells) args) (valid : result.facts.Valid input) :
    Memory.Loop.Forwarding.rewrite graph candidate result.facts input = some result.graph := by
  obtain ⟨facts, _, scanned⟩ := Option.bind_eq_some_iff.mp success
  obtain ⟨rewritten, accepted, returned⟩ := Option.bind_eq_some_iff.mp scanned
  cases Option.some.inj returned
  exact Memory.Loop.Forwarding.rewriteWith_checked accepted valid

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Static.Proofs
