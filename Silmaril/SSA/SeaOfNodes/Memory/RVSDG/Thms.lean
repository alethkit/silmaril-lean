module

public import Silmaril.SSA.SeaOfNodes.Memory.RVSDG.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.RVSDG.Correctness

/-! # Ordered memory lowering preserves the returned word and heap -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory

open RVSDG (Tuple)
open RVSDG.OrderedRuntime.Structured (EntryChecked withRuntime)

variable {args : List ValueSort} {cells : Nat}

/-- The numbered graph is admitted by the canonical single-runtime check. -/
def Graph.lowerChecked (graph : Graph args) :
    EntryChecked (inputData args) wordData graph.lower.toTerm :=
  graph.lowered.checked.collect

/-- The target leaf observes the heap and forwards exactly the same value. -/
theorem load_threads_heap (address : Address cells) (heap : Heap cells) :
    (leafModel cells).toRVSDG.run (.ordered (.value .nil) wordData (.effect .load))
      (withRuntime heap (.cons address .nil)) = encodeResult (heap.read address) heap :=
  RVSDGProofs.load_run address heap

/-- The target evaluator returns the same word and final heap as the source fold. -/
theorem Graph.lower_run (graph : Graph args) (input : Tuple (Val cells) args) (heap : Heap cells) :
    graph.lower.run (leafModel cells).toRVSDG (encodeInput heap input) =
      let result := graph.denote input heap
      encodeResult result.1 result.2 :=
  RVSDGProofs.lower_run graph input heap

/-- The source relation preserves and reflects the target's full output tuple. -/
theorem Graph.lower_returns_iff (graph : Graph args) (input : Tuple (Val cells) args)
    (heap : Heap cells) (value : Word) (final : Heap cells) :
    graph.Returns input heap value final ↔
      graph.lower.run (leafModel cells).toRVSDG (encodeInput heap input) = encodeResult value final :=
  RVSDGProofs.lower_returns_iff graph input heap value final

end Silmaril.SSA.SeaOfNodes.Memory
