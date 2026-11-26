module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Institution.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Institution.Proofs

open CategoryTheory
open Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution renaming
  Signature → EntrySignature, Equation → NativeEquation
open RVSDG (Tuple)

variable {P Q : EntrySignature} {args : List ValueSort}

theorem observe_emit (graph : Graph args) (input : Tuple (Val 2) args)
    (guard : Bool) (initial : Heap 2) :
    (emit graph).observe input guard initial =
      let result := graph.denote guard input initial
      some (encodeResult result.1 result.2) :=
  lower_run graph guard input initial 3

theorem observe_iff_returns (graph : Graph args) (input : Tuple (Val 2) args)
    (guard : Bool) (initial : Heap 2) (word : Word) (final : Heap 2) :
    (emit graph).observe input guard initial = some (encodeResult word final) ↔
      graph.Returns guard input initial word final := by
  constructor
  · intro run
    exact (MLIR.returns_iff graph guard input initial word final).2 ⟨3, run⟩
  · intro returned
    rw [observe_emit, (graph.returns_iff_denote guard input initial word final).1 returned]

theorem translated_satisfaction (e : NativeEquation P) (input : Valuation P) :
    (room P).Sat (Discrete.mk input) (translateEquation e) ↔ e.Holds (nativeModel input) := by
  constructor
  · intro holds
    apply (e.holds_iff_returns (nativeModel input)).2
    intro guard initial word final
    have equal : (emit e.lhs).observe input guard initial = (emit e.rhs).observe input guard initial :=
      holds guard initial
    have same : (emit e.lhs).observe input guard initial = some (encodeResult word final) ↔
        (emit e.rhs).observe input guard initial = some (encodeResult word final) := by rw [equal]
    exact (observe_iff_returns e.lhs input guard initial word final).symm.trans
      (same.trans (observe_iff_returns e.rhs input guard initial word final))
  · intro holds guard initial
    exact (observe_emit e.lhs input guard initial).trans
      ((congrArg (fun result : Word × Heap 2 => some (encodeResult result.1 result.2))
        (holds guard initial)).trans (observe_emit e.rhs input guard initial).symm)

theorem behavior_mapGraph (h : P ⟶ Q) (graph : Graph P.args) (input : Valuation Q)
    (guard : Bool) (initial : Heap 2) :
    (emit (Diamond.Institution.mapGraph h graph)).observe input guard initial =
      (emit graph).observe (pullback h input) guard initial :=
  (observe_emit (Diamond.Institution.mapGraph h graph) input guard initial).trans
    ((congrArg (fun result : Word × Heap 2 => some (encodeResult result.1 result.2))
      (Diamond.Institution.observe_mapGraph h (nativeModel input) graph guard initial)).trans
      (observe_emit graph (pullback h input) guard initial).symm)

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Institution.Proofs
