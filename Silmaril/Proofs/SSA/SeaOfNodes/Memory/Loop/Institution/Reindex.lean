module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Proofs

open CategoryTheory
open Memory.Diamond.Institution
  (Signature Model PortMap mapBody mapBody_id mapBody_comp denote_mapBody pullInput_get reduct)

variable {P Q R : Signature}

theorem mapGraph_id (graph : Graph P.args) : mapGraph (𝟙 P) graph = graph := by
  cases graph
  simp only [mapGraph, Graph.mk.injEq]
  exact ⟨mapBody_id _, rfl⟩

theorem mapGraph_comp (h : P ⟶ Q) (k : Q ⟶ R) (graph : Graph P.args) :
    mapGraph (h ≫ k) graph = mapGraph k (mapGraph h graph) := by
  simp only [mapGraph, Graph.mk.injEq]
  exact ⟨mapBody_comp (Signature.Hom.port h) (Signature.Hom.port k) _, rfl⟩

theorem step_mapGraph (h : P ⟶ Q) (graph : Graph P.args) (model : Model Q) (heap : Heap model.cells) :
    (mapGraph h graph).step model.input heap = graph.step (reduct h model).input heap := by
  let rename : PortMap P.args Q.args := Signature.Hom.port h
  have body := denote_mapBody rename graph.body model.input PUnit.unit heap
  have stop := (pullInput_get rename model.input graph.stop).symm
  exact congrArg₂ (fun (result : Word × Heap model.cells) (stop : Word) =>
    if result.1 = stop then Sum.inl result else Sum.inr result.2) body stop

theorem denote_mapGraph (h : P ⟶ Q) (graph : Graph P.args) (model : Model Q) (initial : Heap model.cells) :
    (mapGraph h graph).denote model.input initial = graph.denote (reduct h model).input initial :=
  congrArg (fun step => Silmaril.Elgot.Part.run step initial)
    (funext fun heap => congrArg Part.some (step_mapGraph h graph model heap))

theorem holds_iff_returns (e : Equation P) (model : Model P) :
    e.Holds model ↔ ∀ (initial : Heap model.cells) word final,
      e.lhs.Returns model.input initial word final ↔ e.rhs.Returns model.input initial word final := by
  simp only [Graph.returns_iff_mem_denote]
  constructor
  · intro holds initial word final
    rw [holds initial]
  · intro holds initial
    exact Part.ext (fun (word, final) => holds initial word final)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Proofs
