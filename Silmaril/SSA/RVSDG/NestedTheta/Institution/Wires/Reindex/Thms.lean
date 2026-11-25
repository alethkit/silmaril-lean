module

public import Silmaril.SSA.RVSDG.NestedTheta.Institution.Wires.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Institution.Partial.Thms
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Institution.Wires.Reindex

/-! # Admission and erasure under opcode relabelling -/

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Institution.Wires

open CategoryTheory
open ExplicitRuntime (Checked EntryChecked)
open OrderedRuntime.Structured (Data Threaded Ty runtime)

universe u v
variable {V : Type u} {A B C : Partial.Signature.{u,v} V}
variable {args outs : Ports (Ty V)} {past sigs : List (Ports (Ty V))}
variable {a : Data args} {b : Data outs} {live : Origin (Threaded args) past runtime}

noncomputable def mapChecked (f : A ⟶ B) {t : Term (WireOp A) (Threaded args) past sigs (Threaded outs)}
    (h : Checked A.base.pure A.base.effect a b live t) :
    Checked B.base.pure B.base.effect a b live (Institution.mapTerm (wireOpcodeMap f) t) :=
  Proofs.mapChecked f h

/-- Relabelling the numbered graph preserves its single-token admission. -/
theorem mapGraph_checked (f : A ⟶ B) (g : Graph (WireOp A) (Threaded args) [] sigs (Threaded outs))
    (h : Nonempty (EntryChecked (a := a) (b := b) g.toTerm)) :
    Nonempty (EntryChecked (a := a) (b := b) (mapGraph f g).toTerm) := by
  rw [mapGraph, Institution.mapGraph, Term.toTerm_toGraph]
  exact h.map (mapChecked f)

theorem checked_erase_eq {t : Term (WireOp A) (Threaded args) past sigs (Threaded outs)}
    (h : Checked A.base.pure A.base.effect a b live t) :
    h.erase = Institution.mapTerm (eraseOpcode A) t :=
  Proofs.erase_eq_mapTerm h

theorem eraseGraph_eq (g : Graph (WireOp A) (Threaded args) [] sigs (Threaded outs))
    (h : EntryChecked (a := a) (b := b) g.toTerm) : eraseGraph g = h.erase.toGraph := by
  rw [checked_erase_eq]
  rfl

theorem mapThreadedOpcode_injective {P Q : Dialect.{u,v} V PUnit.{u+1}}
    (f : RVSDG.Institution.OpcodeMap P Q) (hf : ∀ ins outs, Function.Injective (@f ins outs)) :
    ∀ ins outs, Function.Injective (@mapThreadedOpcode V P Q f ins outs) :=
  Proofs.threaded_injective f hf

/-- Relabel typed unit-slot declarations. Effect injectivity still holds
because a unit-ending signature uniquely determines its data ports. -/
@[expose] def erasedHom (f : A ⟶ B) : erasedSignature A ⟶ erasedSignature B :=
  ⟨erasedBaseHom f, mapThreadedOpcode_injective _ f.effect_injective⟩

theorem eraseGraph_map (f : A ⟶ B) (g : Graph (WireOp A) args past sigs outs) :
    eraseGraph (mapGraph f g) = Institution.mapGraph (Partial.Signature.Hom.opcodeMap (erasedHom f)) (eraseGraph g) :=
  Proofs.eraseGraph_map f g

@[expose] def Equation.map (f : A ⟶ B) (e : Equation A) : Equation B :=
  ⟨e.args, e.outs, e.inputData, e.outputData, e.leftSigs, e.rightSigs, mapGraph f e.lhs, mapGraph f e.rhs,
    mapGraph_checked f e.lhs e.lhsChecked, mapGraph_checked f e.rhs e.rhsChecked⟩

theorem Equation.erase_map (f : A ⟶ B) (e : Equation A) : (e.map f).erase = e.erase.map (erasedHom f) := by
  cases e
  simp only [Equation.erase, Equation.map, Partial.Equation.map, Institution.Equation.map, eraseGraph_map]

theorem Equation.map_id (e : Equation A) : e.map (𝟙 A) = e := by
  cases e
  simp only [Equation.map, Proofs.mapGraph_id]

theorem Equation.map_comp (f : A ⟶ B) (g : B ⟶ C) (e : Equation A) :
    e.map (f ≫ g) = (e.map f).map g := by
  cases e
  simp only [Equation.map, Proofs.mapGraph_comp]

end Silmaril.SSA.RVSDG.NestedTheta.Institution.Wires
