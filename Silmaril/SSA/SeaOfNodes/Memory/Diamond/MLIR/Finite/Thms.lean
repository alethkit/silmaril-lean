module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Finite.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.MLIR.Finite.Correctness

/-! Exact finite execution of the indexed scalar heap lowering. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Finite

open RVSDG (Tuple)
open Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution renaming
  Signature → EntrySignature, Equation → NativeEquation

variable {args : List ValueSort} {P : EntrySignature}

/-- Every budget that reaches the suffix returns the native word and all
cells in index order. Smaller budgets have no return. -/
theorem lower_run (p : Profile) (graph : Graph args) (guard : Bool) (input : Tuple (Val p.cells) args)
    (initial : Heap p.cells) (fuel : Nat) :
    (lower p graph).run evalOp fuel (encodeEntry p guard input initial) =
      if fuel < 3 then none else
        let result := graph.denote guard input initial
        some (encodeResult p result.1 result.2) :=
  Proofs.lower_run p graph guard input initial fuel

theorem encodeResult_injective (p : Profile) :
    Function.Injective (fun result : Word × Heap p.cells => encodeResult p result.1 result.2) :=
  Proofs.encodeResult_injective p

/-- Preserve and reflect the exact finite word and whole initialized heap
at the chosen cell count, for either source guard. -/
theorem returns_iff (p : Profile) (graph : Graph args) (guard : Bool) (input : Tuple (Val p.cells) args)
    (initial : Heap p.cells) (word : Word) (final : Heap p.cells) :
    graph.Returns guard input initial word final ↔ Returns p graph guard input initial word final :=
  Proofs.returns_iff p graph guard input initial word final

/-- Compare emitted CFGs at any checked profile with the native equation at
that cell count and typed valuation. -/
theorem equation_satisfaction (p : Profile) (e : NativeEquation P)
    (input : Tuple (Val p.cells) P.args) :
    (∀ guard initial, observe p e.lhs guard input initial = observe p e.rhs guard input initial) ↔
      e.Holds ⟨p.cells, input⟩ :=
  Proofs.equation_satisfaction p e input

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Finite
