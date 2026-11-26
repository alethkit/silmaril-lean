module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.ToRVSDG.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Thms
public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.RVSDG.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.Institution.ToRVSDG.Adequacy

/-! Satisfaction and typed-entry reindexing for numbered memory diamonds. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.ToRVSDG

open CategoryTheory
open RVSDG (Tuple)

variable {P Q : Signature}

/-- The actual numbered evaluator returns this word and whole heap exactly
when the source occurrence-indexed rules do. -/
theorem observe_iff_returns (graph : Graph P.args) (model : Model P) (guard : Bool)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    (Program.ofGraph graph).observe model guard initial = encodeResult word final ↔
      graph.Returns guard model.input initial word final :=
  (graph.lower_returns_iff guard model.input initial word final).symm

/-- The translated equation has the same truth for both guards and all
initial heaps at this native model's typed entry valuation. -/
theorem translated_satisfaction (e : Equation P) (model : Model P) :
    (room P).Sat (Discrete.mk model) (translateEquation e) ↔ e.Holds model :=
  Proofs.translated_satisfaction e model

/-- Re-emission after a typed entry-port map commutes with model pullback
on the returned word and the whole final heap. -/
theorem behavior_mapGraph (h : P ⟶ Q) (graph : Graph P.args) (model : Model Q)
    (guard : Bool) (initial : Heap model.cells) :
    (Program.ofGraph (mapGraph h graph)).observe model guard initial =
      (Program.ofGraph graph).observe (reduct h model) guard initial :=
  Proofs.behavior_mapGraph h graph model guard initial

/-- Satisfaction commutes with typed entry-port maps on the image of
the lowering. -/
theorem room_satisfaction_reindex (h : P ⟶ Q) (e : Equation P) (model : Model Q) :
    (room Q).Sat (Discrete.mk model) (translateEquation (e.map h)) ↔
      (room P).Sat (Discrete.mk (reduct h model)) (translateEquation e) :=
  (translated_satisfaction (e.map h) model).trans
    ((e.satisfaction h model).trans (translated_satisfaction e (reduct h model)).symm)

/-- With the same Region order on both sides, the existing RVSDG room at
the canonical heap model agrees with the scoped comparison quantified
over every typed entry valuation at that cell count. -/
theorem shared_input_satisfaction (e : CompiledEquation P)
    (aligned : e.lhs.merge = e.rhs.merge) (cells : Nat) :
    (RVSDG.Institution.room.{0, 0, 0} targetSignature).Sat
        (Discrete.mk (leafModel cells).toRVSDG) e.sharedInputEquation ↔
      ∀ input : Tuple (Val cells) P.args, (room P).Sat (Discrete.mk (⟨cells, input⟩ : Model P)) e :=
  Proofs.shared_input_satisfaction e aligned cells

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.ToRVSDG
