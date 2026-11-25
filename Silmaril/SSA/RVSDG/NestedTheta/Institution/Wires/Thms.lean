module

public import Silmaril.SSA.RVSDG.NestedTheta.Institution.Wires.Reindex.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Endpoints.Thms
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Institution.Wires.Satisfaction

/-! # The institution of equations on checked explicit-token graphs -/

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Institution.Wires

open CategoryTheory Silmaril.Logic.Institution
open ExplicitRuntime (EntryChecked boundaryResult)
open OrderedRuntime.Structured (Data RuntimeValues Threaded Ty)

universe u v w
variable {V : Type u} {A B C : Partial.Signature.{u,v} V} {σ : Type (max u w)}
variable {args outs : Ports (Ty V)} {sigs : List (Ports (Ty V))}
variable {a : Data args} {b : Data outs}

/-- Erasure reads the initial store from the explicit input and preserves the
entire returned data and final token. -/
theorem observe_erase (m : Partial.Model.{u,v,w} A σ)
    (g : Graph (WireOp A) (Threaded args) [] sigs (Threaded outs))
    (h : Nonempty (EntryChecked (a := a) (b := b) g.toTerm))
    (input : Tuple (RuntimeValues m.value σ) (Threaded args)) :
    observe m g input = OrderedState.Partial.observe (ExplicitRuntime.Partial.erasedModel m)
      (eraseGraph g) (boundaryResult input).1 (boundaryResult input).2 :=
  Proofs.observe_erase m g h input

/-- The wire and erased graph agree on the precise block and attempt store,
or on the existence of productive divergence. -/
theorem abnormal_erase (m : Partial.Model.{u,v,w} A σ)
    (g : Graph (WireOp A) (Threaded args) [] sigs (Threaded outs))
    (h : Nonempty (EntryChecked (a := a) (b := b) g.toTerm))
    (input : Tuple (RuntimeValues m.value σ) (Threaded args))
    (obs : ExplicitRuntime.Partial.Observation m) :
    ExplicitRuntime.Partial.abnormal m g input obs ↔
      OrderedState.Partial.abnormal (ExplicitRuntime.Partial.erasedModel m)
        (eraseGraph g) (boundaryResult input).1 (boundaryResult input).2 obs :=
  Proofs.abnormal_erase m g h input obs

theorem erasedModel_reduct (f : A ⟶ B) (m : Partial.Model.{u,v,w} B σ) :
    Partial.reduct (erasedHom f) (ExplicitRuntime.Partial.erasedModel m) =
      ExplicitRuntime.Partial.erasedModel (Partial.reduct f m) :=
  Proofs.erasedModel_reduct f m

theorem observe_map (f : A ⟶ B) (m : Partial.Model.{u,v,w} B σ)
    (g : Graph (WireOp A) (Threaded args) [] sigs (Threaded outs))
    (h : Nonempty (EntryChecked (a := a) (b := b) g.toTerm))
    (input : Tuple (RuntimeValues m.value σ) (Threaded args)) :
    observe m (mapGraph f g) input = observe (Partial.reduct f m) g input :=
  Proofs.observe_map f m g h input

/-- The migrated endpoints are exactly the images of the source endpoints.
The relabelling touches only the block's typed opcode. -/
theorem abnormal_map (f : A ⟶ B) (m : Partial.Model.{u,v,w} B σ)
    (g : Graph (WireOp A) (Threaded args) [] sigs (Threaded outs))
    (h : Nonempty (EntryChecked (a := a) (b := b) g.toTerm))
    (input : Tuple (RuntimeValues m.value σ) (Threaded args))
    (obs : ExplicitRuntime.Partial.Observation m) :
    ExplicitRuntime.Partial.abnormal m (mapGraph f g) input obs ↔
      ∃ source, ExplicitRuntime.Partial.abnormal (Partial.reduct f m) g input source ∧
        Partial.mapAbnormal (erasedHom f) source = obs :=
  Proofs.abnormal_map f m g h input obs

theorem abnormal_map_iff (f : A ⟶ B) (m : Partial.Model.{u,v,w} B σ)
    (g : Graph (WireOp A) (Threaded args) [] sigs (Threaded outs))
    (h : Nonempty (EntryChecked (a := a) (b := b) g.toTerm))
    (input : Tuple (RuntimeValues m.value σ) (Threaded args))
    (obs : ExplicitRuntime.Partial.Observation (Partial.reduct f m)) :
    ExplicitRuntime.Partial.abnormal m (mapGraph f g) input (Partial.mapAbnormal (erasedHom f) obs) ↔
      ExplicitRuntime.Partial.abnormal (Partial.reduct f m) g input obs :=
  Proofs.abnormal_map_iff f m g h input obs

theorem Equation.erase_holds (e : Equation A) (m : Partial.Model.{u,v,w} A σ) :
    e.erase.Holds (ExplicitRuntime.Partial.erasedModel m) ↔ e.Holds m :=
  Proofs.erase_holds e m

theorem Equation.satisfaction (f : A ⟶ B) (e : Equation A) (m : Partial.Model.{u,v,w} B σ) :
    (e.map f).Holds m ↔ e.Holds (Partial.reduct f m) := by
  rw [← Equation.erase_holds (e.map f) m, Equation.erase_map, Partial.Equation.satisfaction,
    erasedModel_reduct, Equation.erase_holds]

@[expose] def corridor (f : A ⟶ B) : room A σ ⟶ room B σ :=
  ⟨Equation.map f, Partial.reductFunctor f, fun m e => e.satisfaction f m.as⟩

theorem corridor_id (A : Partial.Signature.{u,v} V) : corridor (σ := σ) (𝟙 A) = 𝟙 (room A σ) :=
  Room.hom_ext (funext Equation.map_id) (Partial.reductFunctor_id A)

theorem corridor_comp (f : A ⟶ B) (g : B ⟶ C) :
    corridor (σ := σ) (f ≫ g) = corridor f ≫ corridor g :=
  Room.hom_ext (funext (Equation.map_comp f g)) (Partial.reductFunctor_comp f g)

@[expose] def inst (V : Type u) (σ : Type (max u w)) :
    Inst.{max u (v + 1), max u v, max u v, max (u + 1) v (w + 1), max (u + 1) v (w + 1)} where
  Sign := Partial.Signature.{u,v} V
  I := { obj := fun A => room A σ, map := corridor, map_id := corridor_id, map_comp := corridor_comp }

end Silmaril.SSA.RVSDG.NestedTheta.Institution.Wires
