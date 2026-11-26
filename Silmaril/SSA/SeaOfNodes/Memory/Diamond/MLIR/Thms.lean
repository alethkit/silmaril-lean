module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.MLIR.Correctness

/-! Finite execution of the two-cell scalarized diamond in typed MLIR CF. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR

open RVSDG (Tuple)

variable {args : List ValueSort}

/-- One tick each for entry, the selected arm and the shared suffix.
Every sufficient budget returns the source word and both cell values. -/
theorem lower_run (graph : Graph args) (guard : Bool) (input : Tuple (Val 2) args)
    (initial : Heap 2) (fuel : Nat) :
    (lower graph).run evalOp fuel (encodeEntry guard input initial) =
      if fuel < 3 then none else
        let result := graph.denote guard input initial
        some (encodeResult result.1 result.2) :=
  Proofs.lower_run graph guard input initial fuel

/-- Preserve and reflect the exact finite word and entire two-cell heap
under either guard, using the emitted CF program. -/
theorem returns_iff (graph : Graph args) (guard : Bool) (input : Tuple (Val 2) args)
    (initial : Heap 2) (word : Word) (final : Heap 2) :
    graph.Returns guard input initial word final ↔ Returns graph guard input initial word final :=
  Proofs.returns_iff graph guard input initial word final

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR
