module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Petri.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Petri.Completion
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Petri.Order
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Theta.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms

/-! # Finite coloured firing observations for the memory loop -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop

open Relation (ReflTransGen)
open RVSDG (Tuple)
open RVSDG.OrderedRuntime.Structured (Threaded runtimePort)
open RVSDG.NestedTheta.Petri (Fire Finishes Marking finished pending finishes_iff)

variable {args : List ValueSort} {cells : Nat}

/-- The generated body has a single designated heap chain. -/
theorem Graph.thetaBody_heap_chain (graph : Graph args) :
    Firing.HeapChain ThetaOpcode (carrier args) (Threaded (tagged args))
      (.arg (runtimePort (dataPorts args))) graph.thetaBody :=
  Firing.Proofs.theta_chain graph

/-- Every reachable child marking contains a completed prefix of the
declared activation order and a pending suffix. -/
theorem Graph.activation_reachable_prefix (graph : Graph args) (input : Tuple (Val cells) args)
    (heap : Heap cells) {mark : Marking (thetaRuntime cells) (.ofBase graph.thetaBody)}
    (trace : ReflTransGen
      (Fire (past := []) (thetaRuntime cells) (.ofBase graph.thetaBody) (encodeInput heap input) PUnit.unit)
      (pending (thetaRuntime cells) (.ofBase graph.thetaBody)) mark) :
    ∃ count, Firing.DonePrefix (thetaRuntime cells) (.ofBase graph.thetaBody) mark count :=
  Firing.Proofs.activation_reachable graph input heap trace

/-- A single firing advances the completed prefix by exactly one vertex. -/
theorem Graph.activation_firing_step (graph : Graph args) (input : Tuple (Val cells) args)
    (heap : Heap cells) {before after : Marking (thetaRuntime cells) (.ofBase graph.thetaBody)} {count : Nat}
    (done : Firing.DonePrefix (thetaRuntime cells) (.ofBase graph.thetaBody) before count)
    (step : Fire (past := []) (thetaRuntime cells) (.ofBase graph.thetaBody)
      (encodeInput heap input) PUnit.unit before after) :
    Firing.DonePrefix (thetaRuntime cells) (.ofBase graph.thetaBody) after (count + 1) :=
  Firing.Proofs.prefix_step graph.thetaBody_heap_chain (encodeInput heap input) PUnit.unit done step

/-- A completed activation has reached the end of its declared prefix. -/
theorem Graph.activation_completed_length (graph : Graph args) (input : Tuple (Val cells) args)
    (heap : Heap cells) {mark : Marking (thetaRuntime cells) (.ofBase graph.thetaBody)} {count : Nat}
    {output : Tuple (WireVal cells) (RVSDG.Theta.BodyResults (carrier args))}
    (done : Firing.DonePrefix (thetaRuntime cells) (.ofBase graph.thetaBody) mark count)
    (result : finished (past := []) (thetaRuntime cells) (.ofBase graph.thetaBody)
      (encodeInput heap input) PUnit.unit mark = some output) :
    count = graph.thetaSigs.length :=
  Firing.Proofs.completed_prefix_length (model := thetaRuntime cells) (past := [])
    (.ofBase graph.thetaBody) (encodeInput heap input) PUnit.unit done result

/-- A genuine completed firing sequence of the numbered activation observes
exactly the tag and heap of the ordered body. -/
theorem Graph.activation_finishes_iff (graph : Graph args) (input : Tuple (Val cells) args)
    (heap : Heap cells) (output : Tuple (WireVal cells) (RVSDG.Theta.BodyResults (carrier args))) :
    Finishes (thetaRuntime cells) graph.activation (encodeInput heap input) output ↔
      let body := graph.body.denote input heap
      Tuple.cons (F := WireVal cells) (t := .control 2)
        (continueTag body.1 (graph.stopWord input)) (encodeInput body.2 input) = output :=
  Firing.Proofs.activation_finishes graph input heap output

/-- Finite completion of the actual numbered θ preserves and reflects the
source return word and entire final heap. -/
theorem Graph.lowerTheta_finishes_iff (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Heap cells) (value : Word) (final : Heap cells) :
    graph.Returns input initial value final ↔
      Finishes (thetaRuntime cells) graph.lowerTheta (encodeInput initial input) (encodeResult value final) :=
  (graph.lowerTheta_returns_iff input initial value final).trans (finishes_iff _ _ _ _).symm

end Silmaril.SSA.SeaOfNodes.Memory.Loop
