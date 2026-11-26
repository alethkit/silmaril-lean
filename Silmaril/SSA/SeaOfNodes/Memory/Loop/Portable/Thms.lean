module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Portable.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Thms
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.LambdaSSA.Thms
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Theta.Thms
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Petri.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Portable.Observation

/-! # Portable finite-return agreement for the whole-memory loop -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop

open RVSDG (Tuple)

variable {args : List ValueSort} {cells : Nat}

/-- The counted native return certifies the same word and whole heap in
the actual typed λSSA CFG, numbered θ and coloured Petri completion. -/
theorem Graph.returnsAfter_iff_portable (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Heap cells) (backedges : Nat) (word : Word) (final : Heap cells) :
    graph.ReturnsAfter input initial backedges word final ↔
      Portable.Observation graph input initial backedges word final :=
  Proofs.SSA.SeaOfNodes.Memory.Loop.Portable.returnsAfter_iff graph input initial backedges word final

/-- The ordinary finite return admits the same portable observation at
some exact source backedge count. -/
theorem Graph.returns_iff_portable (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Heap cells) (word : Word) (final : Heap cells) :
    graph.Returns input initial word final ↔
      ∃ backedges, Portable.Observation graph input initial backedges word final :=
  exists_congr fun backedges => graph.returnsAfter_iff_portable input initial backedges word final

end Silmaril.SSA.SeaOfNodes.Memory.Loop
