module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.RVSDG.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.RVSDG.Correctness
import Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Thms

/-! # Ordered γ executes the selected arm and the common suffix -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond

open RVSDG (Tuple)
open RVSDG.OrderedRuntime.Structured (EntryChecked)
open SeaOfNodes.Diamond (Projection)

variable {args : List ValueSort} {cells : Nat}

/-- The numbered RVSDG has one live heap at every boundary. -/
def Graph.lowerChecked (graph : Graph args) :
    EntryChecked (diamondData args) wordData graph.lower.toTerm :=
  graph.lowered.checked.collect

/-- The numbered evaluator executes just the selected arm and starts the
suffix with its returned word and whole heap. -/
theorem Graph.lower_run_selected (graph : Graph args) (guard : Bool)
    (input : Tuple (Val cells) args) (heap : Heap cells) :
    graph.lower.run (leafModel cells).toRVSDG (graph.encodeEntry guard input heap) =
      let selected := (graph.arm (Projection.ofBool guard)).lower.run
        (leafModel cells).toRVSDG (encodeInput heap input)
      graph.suffix.lower.run (leafModel cells).toRVSDG
        (encodeInput (selected.get (.tail .head)) (.cons (selected.get .head) input)) :=
  RVSDGProofs.lower_run_selected graph guard input heap

theorem Graph.lower_run (graph : Graph args) (guard : Bool)
    (input : Tuple (Val cells) args) (heap : Heap cells) :
    graph.lower.run (leafModel cells).toRVSDG (graph.encodeEntry guard input heap) =
      let result := graph.denote guard input heap
      encodeResult result.1 result.2 :=
  RVSDGProofs.lower_run graph guard input heap

/-- Preserve and reflect the full source observation, including final memory. -/
theorem Graph.lower_returns_iff (graph : Graph args) (guard : Bool)
    (input : Tuple (Val cells) args) (heap : Heap cells) (value : Word) (final : Heap cells) :
    graph.Returns guard input heap value final ↔
      graph.lower.run (leafModel cells).toRVSDG (graph.encodeEntry guard input heap) =
        encodeResult value final :=
  RVSDGProofs.lower_returns_iff graph guard input heap value final

end Silmaril.SSA.SeaOfNodes.Memory.Diamond
