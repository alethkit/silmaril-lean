module

public import Silmaril.SSA.RVSDG.NestedTheta.Institution.Wires.Reindex.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Endpoints.Thms

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Institution.Wires.Proofs

open CategoryTheory
open ExplicitRuntime (EntryChecked boundaryResult boundaryResult_bijective)
open OrderedRuntime.Structured (Data RuntimeValues Threaded Ty Values)

universe u v w
variable {V : Type u} {A B : Institution.Partial.Signature.{u,v} V} {σ : Type (max u w)}
variable {args outs : Ports (Ty V)} {sigs : List (Ports (Ty V))}
variable {a : Data args} {b : Data outs}

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem observe_erase (m : Institution.Partial.Model.{u,v,w} A σ)
    (g : Graph (WireOp A) (Threaded args) [] sigs (Threaded outs))
    (h : Nonempty (EntryChecked (a := a) (b := b) g.toTerm))
    (input : Tuple (RuntimeValues m.value σ) (Threaded args)) :
    observe m g input = OrderedState.Partial.observe (ExplicitRuntime.Partial.erasedModel m)
      (eraseGraph g) (boundaryResult input).1 (boundaryResult input).2 := by
  obtain ⟨h⟩ := h
  rw [eraseGraph_eq g h]
  exact ExplicitRuntime.Partial.observe_eq m g h input

theorem abnormal_erase (m : Institution.Partial.Model.{u,v,w} A σ)
    (g : Graph (WireOp A) (Threaded args) [] sigs (Threaded outs))
    (h : Nonempty (EntryChecked (a := a) (b := b) g.toTerm))
    (input : Tuple (RuntimeValues m.value σ) (Threaded args))
    (obs : ExplicitRuntime.Partial.Observation m) :
    ExplicitRuntime.Partial.abnormal m g input obs ↔
      OrderedState.Partial.abnormal (ExplicitRuntime.Partial.erasedModel m)
        (eraseGraph g) (boundaryResult input).1 (boundaryResult input).2 obs := by
  obtain ⟨h⟩ := h
  rw [eraseGraph_eq g h]
  exact ExplicitRuntime.Partial.abnormal_iff m g h input obs

theorem erasedModel_reduct (f : A ⟶ B) (m : Institution.Partial.Model.{u,v,w} B σ) :
    Institution.Partial.reduct (erasedHom f) (ExplicitRuntime.Partial.erasedModel m) =
      ExplicitRuntime.Partial.erasedModel (Institution.Partial.reduct f m) := by
  unfold Institution.Partial.reduct ExplicitRuntime.Partial.erasedModel
  congr 1
  all_goals
    funext ins outs op input
    cases op
    simp only [erasedHom, erasedBaseHom, mapThreadedOpcode]

private theorem orderedObserve_congr
    {m n : Institution.Partial.Model.{u,v,w} A σ} (equal : m = n)
    (g : Graph A.base.op args [] sigs outs)
    (x : Tuple (Values m.value) args) (y : Tuple (Values n.value) args)
    (inputs : HEq x y) (store : σ) :
    HEq (OrderedState.Partial.observe m g x store) (OrderedState.Partial.observe n g y store) := by
  cases equal
  cases inputs
  rfl

private theorem orderedAbnormal_congr
    {m n : Institution.Partial.Model.{u,v,w} A σ} (equal : m = n)
    (g : Graph A.base.op args [] sigs outs)
    (x : Tuple (Values m.value) args) (y : Tuple (Values n.value) args)
    (inputs : HEq x y) (store : σ)
    (left : OrderedState.Partial.Abnormal A.base.effect m.value σ)
    (right : OrderedState.Partial.Abnormal A.base.effect n.value σ) (observations : HEq left right) :
    OrderedState.Partial.abnormal m g x store left ↔ OrderedState.Partial.abnormal n g y store right := by
  cases equal
  cases inputs
  cases observations
  rfl

theorem observe_map (f : A ⟶ B) (m : Institution.Partial.Model.{u,v,w} B σ)
    (g : Graph (WireOp A) (Threaded args) [] sigs (Threaded outs))
    (h : Nonempty (EntryChecked (a := a) (b := b) g.toTerm))
    (input : Tuple (RuntimeValues m.value σ) (Threaded args)) :
    observe m (mapGraph f g) input = observe (Institution.Partial.reduct f m) g input := by
  rw [observe_erase m _ (mapGraph_checked f g h), eraseGraph_map]
  rw [Institution.Partial.observe_map (erasedHom f) (ExplicitRuntime.Partial.erasedModel m)
    (eraseGraph g) (boundaryResult input).1 (boundaryResult input).2]
  have same := orderedObserve_congr (erasedModel_reduct f m) (eraseGraph g)
    (boundaryResult input).1 (boundaryResult input).1 HEq.rfl (boundaryResult input).2
  exact (eq_of_heq same).trans (observe_erase (Institution.Partial.reduct f m) g h input).symm

theorem abnormal_map (f : A ⟶ B) (m : Institution.Partial.Model.{u,v,w} B σ)
    (g : Graph (WireOp A) (Threaded args) [] sigs (Threaded outs))
    (h : Nonempty (EntryChecked (a := a) (b := b) g.toTerm))
    (input : Tuple (RuntimeValues m.value σ) (Threaded args))
    (obs : ExplicitRuntime.Partial.Observation m) :
    ExplicitRuntime.Partial.abnormal m (mapGraph f g) input obs ↔
      ∃ source, ExplicitRuntime.Partial.abnormal (Institution.Partial.reduct f m) g input source ∧
        Institution.Partial.mapAbnormal (erasedHom f) source = obs := by
  rw [abnormal_erase m _ (mapGraph_checked f g h), eraseGraph_map]
  rw [Institution.Partial.abnormal_map (erasedHom f) (ExplicitRuntime.Partial.erasedModel m)
    (eraseGraph g) (boundaryResult input).1 (boundaryResult input).2 obs]
  refine exists_congr fun source => and_congr ?_ Iff.rfl
  have same := orderedAbnormal_congr (erasedModel_reduct f m) (eraseGraph g)
    (boundaryResult input).1 (boundaryResult input).1 HEq.rfl (boundaryResult input).2 source source HEq.rfl
  exact same.trans (abnormal_erase (Institution.Partial.reduct f m) g h input source).symm

theorem abnormal_map_iff (f : A ⟶ B) (m : Institution.Partial.Model.{u,v,w} B σ)
    (g : Graph (WireOp A) (Threaded args) [] sigs (Threaded outs))
    (h : Nonempty (EntryChecked (a := a) (b := b) g.toTerm))
    (input : Tuple (RuntimeValues m.value σ) (Threaded args))
    (obs : ExplicitRuntime.Partial.Observation (Institution.Partial.reduct f m)) :
    ExplicitRuntime.Partial.abnormal m (mapGraph f g) input
        (Institution.Partial.mapAbnormal (erasedHom f) obs) ↔
      ExplicitRuntime.Partial.abnormal (Institution.Partial.reduct f m) g input obs := by
  rw [abnormal_erase m _ (mapGraph_checked f g h), eraseGraph_map]
  rw [Institution.Partial.abnormal_map_iff (erasedHom f) (ExplicitRuntime.Partial.erasedModel m)
    (eraseGraph g) (boundaryResult input).1 (boundaryResult input).2 obs]
  have same := orderedAbnormal_congr (erasedModel_reduct f m) (eraseGraph g)
    (boundaryResult input).1 (boundaryResult input).1 HEq.rfl (boundaryResult input).2 obs obs HEq.rfl
  exact same.trans (abnormal_erase (Institution.Partial.reduct f m) g h input obs).symm

theorem erase_holds (e : Equation A) (m : Institution.Partial.Model.{u,v,w} A σ) :
    e.erase.Holds (ExplicitRuntime.Partial.erasedModel m) ↔ e.Holds m := by
  constructor
  · intro holds input
    refine ⟨?_, ?_⟩
    · rw [observe_erase m e.lhs e.lhsChecked, observe_erase m e.rhs e.rhsChecked]
      exact (holds _ _).1
    · intro obs
      rw [abnormal_erase m e.lhs e.lhsChecked, abnormal_erase m e.rhs e.rhsChecked]
      exact (holds _ _).2 obs
  · intro holds entry store
    obtain ⟨input, h⟩ := (boundaryResult_bijective e.inputData).2 (entry, store)
    have left : (boundaryResult input).1 = entry := congrArg Prod.fst h
    have right : (boundaryResult input).2 = store := congrArg Prod.snd h
    rw [← left, ← right]
    refine ⟨?_, ?_⟩
    · exact (observe_erase m e.lhs e.lhsChecked input).symm.trans
        ((holds input).1.trans (observe_erase m e.rhs e.rhsChecked input))
    · intro obs
      exact (abnormal_erase m e.lhs e.lhsChecked input obs).symm.trans
        (((holds input).2 obs).trans (abnormal_erase m e.rhs e.rhsChecked input obs))

end Silmaril.SSA.RVSDG.NestedTheta.Institution.Wires.Proofs
