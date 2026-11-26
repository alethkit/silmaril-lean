module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Search.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Search.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Search

open RVSDG (Tuple)

variable {args : List ValueSort} {cells : Nat}
variable {source : Loop.Graph args} {result : Result args}

/-- The chosen Store targets the first Load's exact wire. The reported
writers account for every later Store, in newest-first order, and each
uses a different port. Concrete cell inequality is a separate premise. -/
theorem discover_latest (success : discover source = some result) :
    capturedAddress source = some result.facts.observed ∧
      ∃ newer older,
        (stores source.body).reverse =
          newer ++ (result.graph.storeVersion, some result.facts.observed) :: older ∧
        newer.map Prod.snd = result.facts.writers.map some ∧
        ∀ writer ∈ result.facts.writers, writer.index ≠ result.facts.observed.index :=
  (Proofs.discover_spec success).2

theorem discover_accepted (success : discover source = some result) :
    Carried.rewriteWith source result.graph.storeVersion result.facts = some result.graph :=
  (Proofs.discover_spec success).1

theorem discoverChecked_eq_some_iff (input : Tuple (Val cells) args) :
    discoverChecked source input = some result ↔
      discover source = some result ∧ result.facts.Valid input :=
  Proofs.discoverChecked_eq_some_iff input

theorem discover_stored_reads (success : discover source = some result)
    (input : Tuple (Val cells) args) (valid : result.facts.Valid input) (header : Header cells) :
    let out := result.graph.activateWithStore input header
    out.stored = some (out.result.2.read (input.get result.graph.address)) :=
  Carried.rewriteWith_stored_reads (discover_accepted success) input valid header

theorem discover_evalAfter (success : discover source = some result)
    (input : Tuple (Val cells) args) (valid : result.facts.Valid input) (initial : Heap cells) (count : Nat) :
    result.graph.evalAfter input initial count = source.evalAfter input initial count :=
  Carried.rewriteWith_evalAfter (discover_accepted success) input valid initial count

theorem discover_returns_iff (success : discover source = some result)
    (input : Tuple (Val cells) args) (valid : result.facts.Valid input)
    (initial : Heap cells) (word : Word) (final : Heap cells) :
    result.graph.Returns input initial word final ↔ source.Returns input initial word final :=
  Carried.rewriteWith_returns_iff (discover_accepted success) input valid initial word final

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Search
