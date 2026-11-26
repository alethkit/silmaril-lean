module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Portable.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.LambdaSSA.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Theta.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Petri.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Portable

open Silmaril.SSA.RVSDG (Tuple)
open Silmaril.SSA.SeaOfNodes.Memory (Heap Val ValueSort Word)
open Silmaril.SSA.SeaOfNodes.Memory.Loop
open Silmaril.SSA.SeaOfNodes.Memory.Loop.Portable (Observation)

variable {args : List ValueSort} {cells : Nat}

theorem returnsAfter_iff (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Heap cells) (backedges : Nat) (word : Word) (final : Heap cells) :
    graph.ReturnsAfter input initial backedges word final ↔
      Observation graph input initial backedges word final := by
  have count := LambdaSSA.returnsAfter_iff graph input initial backedges word final
  constructor
  · intro source
    have returned : graph.Returns input initial word final := ⟨backedges, source⟩
    obtain ⟨before, atExit⟩ := (graph.lowerTheta_returnsAfter_iff input initial backedges word final).mp source
    exact ⟨LambdaSSA.lower_hasType graph, (LambdaSSA.returns_iff graph input initial word final).mp returned,
      count.mp source, before, atExit, (graph.lowerTheta_finishes_iff input initial word final).mp returned⟩
  · exact fun observed => count.mpr observed.lambdaCounted

end Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Portable
