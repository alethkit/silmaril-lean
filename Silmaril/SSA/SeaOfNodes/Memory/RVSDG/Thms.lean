module

public import Silmaril.SSA.SeaOfNodes.Memory.RVSDG.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.RVSDG.Correctness

/-! # Ordered memory lowering preserves the returned word and heap -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory

open RVSDG (Locals Origin Port Tuple)
open RVSDG.OrderedRuntime.Structured (Data EntryChecked Threaded Ty readOrigin runtime withRuntime)

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

theorem encodeInput_get {sort : ValueSort} (port : Port args sort)
    (input : Tuple (Val cells) args) (heap : Heap cells) :
    (encodeInput heap input).get (argumentPort port) = input.get port :=
  RVSDGProofs.encodeInput_get port input heap

/-- Lower a memory body in an enclosing region. The initial heap is read
from the live runtime wire, and the routing must preserve the scalar inputs. -/
theorem Body.lowerAt_eval {past : List (List ValueSort)} {version : Nat}
    {entryPorts : List (Ty ValueSort)} {target : List (List (Ty ValueSort))}
    (body : Body args past version) (data : Data entryPorts)
    (routing : Routing args past target entryPorts) (live : Origin (Threaded entryPorts) target runtime)
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past)
    (entry : Tuple (WireVal cells) (Threaded entryPorts)) (regs : Locals (WireVal cells) target)
    (agree : ∀ {sort} (wire : Origin args past sort),
      readOrigin (routing wire) entry regs = readValue wire input locals) :
    (body.lowerAt data routing live).term.eval (leafModel cells).toRVSDG entry regs =
      let result := body.denote input locals (readOrigin live entry regs)
      encodeResult result.1 result.2 :=
  RVSDGProofs.lowerAt_eval body data routing live input locals entry regs agree

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
