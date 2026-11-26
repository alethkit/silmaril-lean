module

public import Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.MLIR.MemRef.Correctness

/-! Whole-buffer correctness for the initialized rank-one MemRef profile. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef

open RVSDG (Tuple)
open Silmaril.MLIR.MemRef (Buffer)

variable {cells : Nat} {args : List ValueSort}

/-- The initial buffer's cell function is the native initial heap. The
emitted block agrees on the word and every final cell. -/
theorem lower_run (graph : Graph args) (input : Tuple (Val cells) args) (initial : Buffer cells) :
    observe graph input initial =
      let result := graph.denote input initial.cell
      (result.1, ⟨result.2⟩) :=
  Proofs.lower_run graph input initial

/-- The exact word and final buffer preserve and reflect the ordered
source return relation. -/
theorem lower_returns_iff (graph : Graph args) (input : Tuple (Val cells) args) (initial : Heap cells)
    (word : Word) (final : Heap cells) :
    graph.Returns input initial word final ↔ observe graph input ⟨initial⟩ = (word, ⟨final⟩) :=
  Proofs.lower_returns_iff graph input initial word final

end Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef
