module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Institution.Reindex

/-! Typed entry reindexing and finite-return equations. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution

open CategoryTheory Silmaril.Logic.Institution
open Memory.Diamond.Institution (Signature Model reduct reduct_id reduct_comp)

variable {P Q R : Signature}

@[simp] theorem mapGraph_id (graph : Graph P.args) : mapGraph (𝟙 P) graph = graph :=
  Proofs.mapGraph_id graph

theorem mapGraph_comp (h : P ⟶ Q) (k : Q ⟶ R) (graph : Graph P.args) :
    mapGraph (h ≫ k) graph = mapGraph k (mapGraph h graph) :=
  Proofs.mapGraph_comp h k graph

theorem step_mapGraph (h : P ⟶ Q) (graph : Graph P.args) (model : Model Q) (heap : Heap model.cells) :
    (mapGraph h graph).step model.input heap = graph.step (reduct h model).input heap :=
  Proofs.step_mapGraph h graph model heap

/-- Input renaming and model pullback preserve all finite observations. -/
theorem denote_mapGraph (h : P ⟶ Q) (graph : Graph P.args) (model : Model Q) (initial : Heap model.cells) :
    (mapGraph h graph).denote model.input initial = graph.denote (reduct h model).input initial :=
  Proofs.denote_mapGraph h graph model initial

theorem Equation.holds_iff_returns (e : Equation P) (model : Model P) :
    e.Holds model ↔ ∀ (initial : Heap model.cells) word final,
      e.lhs.Returns model.input initial word final ↔ e.rhs.Returns model.input initial word final :=
  Proofs.holds_iff_returns e model

@[simp] theorem Equation.map_id (e : Equation P) : e.map (𝟙 P) = e := by
  cases e
  simp only [Equation.map, mapGraph_id]

theorem Equation.map_comp (h : P ⟶ Q) (k : Q ⟶ R) (e : Equation P) :
    e.map (h ≫ k) = (e.map h).map k := by
  simp only [Equation.map, mapGraph_comp]

theorem Equation.satisfaction (h : P ⟶ Q) (e : Equation P) (model : Model Q) :
    (e.map h).Holds model ↔ e.Holds (reduct h model) := by
  refine forall_congr' fun initial => ?_
  change (mapGraph h e.lhs).denote model.input initial = (mapGraph h e.rhs).denote model.input initial ↔ _
  rw [denote_mapGraph h e.lhs model initial, denote_mapGraph h e.rhs model initial]
  exact Iff.rfl

/-- Reindex the two loop bodies and pull back the shared entry valuation. -/
@[expose] def corridor (h : P ⟶ Q) : room P ⟶ room Q :=
  ⟨Equation.map h, Discrete.functor (fun m => Discrete.mk (reduct h m)),
    fun model e => e.satisfaction h model.as⟩

theorem corridor_id (P : Signature) : corridor (𝟙 P) = 𝟙 (room P) :=
  Room.hom_ext (funext Equation.map_id)
    (Discrete.functor_ext fun m => congrArg Discrete.mk (reduct_id m))

theorem corridor_comp (h : P ⟶ Q) (k : Q ⟶ R) : corridor (h ≫ k) = corridor h ≫ corridor k :=
  Room.hom_ext (funext (Equation.map_comp h k))
    (Discrete.functor_ext fun m => congrArg Discrete.mk (reduct_comp h k m))

/-- Native ordered memory-loop equations over typed entry interfaces. -/
@[expose] def inst : Inst.{0, 0, 0, 0, 0} where
  Sign := Signature
  I := ⟨room, corridor, corridor_id, corridor_comp⟩

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution
