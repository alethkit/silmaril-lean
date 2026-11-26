module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Institution.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.MLIR.Institution.Adequacy

/-! Preservation and reflection at two initialized cells. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Institution

open CategoryTheory
open Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution renaming
  Signature → EntrySignature, Model → NativeModel, Equation → NativeEquation
open RVSDG (Tuple)

variable {P Q : EntrySignature} {args : List ValueSort}

/-- The canonical observation executes all three blocks of the lowered path. -/
theorem observe_emit (graph : Graph args) (input : Tuple (Val 2) args)
    (guard : Bool) (initial : Heap 2) :
    (emit graph).observe input guard initial =
      let result := graph.denote guard input initial
      some (encodeResult result.1 result.2) :=
  Proofs.observe_emit graph input guard initial

/-- The encoded output observes both components of the native return. -/
theorem observe_iff_returns (graph : Graph args) (input : Tuple (Val 2) args)
    (guard : Bool) (initial : Heap 2) (word : Word) (final : Heap 2) :
    (emit graph).observe input guard initial = some (encodeResult word final) ↔
      graph.Returns guard input initial word final :=
  Proofs.observe_iff_returns graph input guard initial word final

/-- Compile both sides and compare the word and both cells, at every guard
and initial heap for this two-cell valuation. -/
theorem translated_satisfaction (e : NativeEquation P) (input : Valuation P) :
    (room P).Sat (Discrete.mk input) (translateEquation e) ↔ e.Holds (nativeModel input) :=
  Proofs.translated_satisfaction e input

/-- Re-emission after a typed entry-port map commutes with valuation pullback
on the actual CFG observations. -/
theorem behavior_mapGraph (h : P ⟶ Q) (graph : Graph P.args) (input : Valuation Q)
    (guard : Bool) (initial : Heap 2) :
    (emit (Diamond.Institution.mapGraph h graph)).observe input guard initial =
      (emit graph).observe (pullback h input) guard initial :=
  Proofs.behavior_mapGraph h graph input guard initial

theorem satisfaction_reindex (h : P ⟶ Q) (e : NativeEquation P) (input : Valuation Q) :
    (room Q).Sat (Discrete.mk input) (translateEquation (e.map h)) ↔
      (room P).Sat (Discrete.mk (pullback h input)) (translateEquation e) :=
  (translated_satisfaction (e.map h) input).trans
    ((e.satisfaction h (nativeModel input)).trans (translated_satisfaction e (pullback h input)).symm)

theorem validity_two_cells (e : NativeEquation P) :
    (∀ input, (room P).Sat (Discrete.mk input) (translateEquation e)) ↔ HoldsTwoCells e :=
  forall_congr' (translated_satisfaction e)

theorem all_models_implies_two_cells (e : NativeEquation P)
    (valid : ∀ model : NativeModel P, e.Holds model) : HoldsTwoCells e :=
  fun input => valid (nativeModel input)

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Institution
