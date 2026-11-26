module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.Institution.Reindex

/-! Typed entry reindexing and satisfaction for native memory diamonds. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution

open CategoryTheory Silmaril.Logic.Institution
open RVSDG (Port Tuple)

variable {P Q R : Signature}
variable {args target : List ValueSort} {cells : Nat}

@[simp] theorem mapGraph_id (graph : Graph P.args) : mapGraph (𝟙 P) graph = graph :=
  Proofs.mapGraph_id graph

theorem mapGraph_comp (h : P ⟶ Q) (k : Q ⟶ R) (graph : Graph P.args) :
    mapGraph (h ≫ k) graph = mapGraph k (mapGraph h graph) :=
  Proofs.mapGraph_comp h k graph

theorem pullInput_get (rename : PortMap args target) (input : Tuple (Val cells) target)
    {sort : ValueSort} (p : Port args sort) :
    (pullInput rename input).get p = input.get (rename p) :=
  Proofs.pullInput_get rename input p

/-- Pullback in the suffix leaves its bound arm result in the first port. -/
theorem pullInput_lift (rename : PortMap args target) (word : Word)
    (input : Tuple (Val cells) target) :
    pullInput (liftPortMap rename) (.cons word input) = .cons word (pullInput rename input) :=
  Proofs.pullInput_lift rename word input

@[simp] theorem reduct_id (model : Model P) : reduct (𝟙 P) model = model :=
  Proofs.reduct_id model

theorem reduct_comp (h : P ⟶ Q) (k : Q ⟶ R) (model : Model R) :
    reduct (h ≫ k) model = reduct h (reduct k model) :=
  Proofs.reduct_comp h k model

/-- The observation pair is exactly the result of the occurrence-indexed
execution rules, including selection by the actual Region input slot. -/
theorem Model.returns_iff_observe (model : Model P) (graph : Graph P.args)
    (guard : Bool) (initial : Heap model.cells) (value : Word) (final : Heap model.cells) :
    graph.Returns guard model.input initial value final ↔
      model.observe graph guard initial = (value, final) :=
  graph.returns_iff_denote guard model.input initial value final

/-- Reindexing the input wires and pulling back the model agree on both
components of the observation at each guard and heap. -/
theorem observe_mapGraph (h : P ⟶ Q) (model : Model Q) (graph : Graph P.args)
    (guard : Bool) (initial : Heap model.cells) :
    model.observe (mapGraph h graph) guard initial = (reduct h model).observe graph guard initial :=
  Proofs.observe_mapGraph h model graph guard initial

/-- The pointwise reindexing law for the occurrence-indexed source rules. -/
theorem returns_mapGraph (h : P ⟶ Q) (model : Model Q) (graph : Graph P.args)
    (guard : Bool) (initial : Heap model.cells) (value : Word) (final : Heap model.cells) :
    (mapGraph h graph).Returns guard model.input initial value final ↔
      graph.Returns guard (reduct h model).input initial value final := by
  refine (model.returns_iff_observe (mapGraph h graph) guard initial value final).trans ?_
  rw [observe_mapGraph h model graph guard initial]
  exact ((reduct h model).returns_iff_observe graph guard initial value final).symm

theorem Equation.holds_iff_returns (e : Equation P) (model : Model P) :
    e.Holds model ↔ ∀ guard (initial : Heap model.cells) value final,
      e.lhs.Returns guard model.input initial value final ↔
        e.rhs.Returns guard model.input initial value final :=
  Proofs.holds_iff_returns e model

@[simp] theorem Equation.map_id (e : Equation P) : e.map (𝟙 P) = e := by
  cases e
  simp only [Equation.map, mapGraph_id]

theorem Equation.map_comp (h : P ⟶ Q) (k : Q ⟶ R) (e : Equation P) :
    e.map (h ≫ k) = (e.map h).map k := by
  simp only [Equation.map, mapGraph_comp]

/-- Satisfaction of the translated sentence in the target model is
equivalent to satisfaction in its typed-entry reduct. -/
theorem Equation.satisfaction (h : P ⟶ Q) (e : Equation P) (model : Model Q) :
    (e.map h).Holds model ↔ e.Holds (reduct h model) := by
  refine forall_congr' fun guard => forall_congr' fun initial => ?_
  change model.observe (mapGraph h e.lhs) guard initial =
    model.observe (mapGraph h e.rhs) guard initial ↔ _
  rw [observe_mapGraph h model e.lhs guard initial, observe_mapGraph h model e.rhs guard initial]
  exact Iff.rfl

/-- Reindex equations forward and pull back entry valuations. -/
@[expose] def corridor (h : P ⟶ Q) : room P ⟶ room Q :=
  ⟨Equation.map h, Discrete.functor (fun m => Discrete.mk (reduct h m)),
    fun model e => e.satisfaction h model.as⟩

theorem corridor_id (P : Signature) : corridor (𝟙 P) = 𝟙 (room P) :=
  Room.hom_ext (funext Equation.map_id)
    (Discrete.functor_ext fun m => congrArg Discrete.mk (reduct_id m))

theorem corridor_comp (h : P ⟶ Q) (k : Q ⟶ R) :
    corridor (h ≫ k) = corridor h ≫ corridor k :=
  Room.hom_ext (funext (Equation.map_comp h k))
    (Discrete.functor_ext fun m => congrArg Discrete.mk (reduct_comp h k m))

/-- The native initialized-cell diamond institution over typed entry interfaces. -/
@[expose] def inst : Inst.{0, 0, 0, 0, 0} where
  Sign := Signature
  I := ⟨room, corridor, corridor_id, corridor_comp⟩

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution
