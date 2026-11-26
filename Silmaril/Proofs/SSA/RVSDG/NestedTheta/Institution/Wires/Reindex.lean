module

public import Silmaril.SSA.RVSDG.NestedTheta.Institution.Wires.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Institution.Partial.Thms

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Institution.Wires.Proofs

open CategoryTheory
open ExplicitRuntime
open OrderedRuntime.Structured (Data Threaded Ty runtime)
open RVSDG.Institution (OpcodeMap)

universe u v
variable {V : Type u} {A B C : Institution.Partial.Signature.{u,v} V}
variable {args outs : Ports (Ty V)} {past sigs : List (Ports (Ty V))}
variable {a : Data args} {b : Data outs} {live : Origin (Threaded args) past runtime}

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable def mapChecked (f : A ⟶ B) {t : Term (WireOp A) (Threaded args) past sigs (Threaded outs)}
    (h : Checked A.base.pure A.base.effect a b live t) :
    Checked B.base.pure B.base.effect a b live (Institution.mapTerm (wireOpcodeMap f) t) := by
  induction h with
  | ret live wires => exact .ret live wires
  | primitive live i o op wires _ ih =>
    simp only [Institution.mapTerm, Node.ofBase, OrderedRuntime.Structured.primitiveNode, wireOpcodeMap]
    convert Checked.primitive live i o (Institution.Partial.Signature.Hom.opcodeMap f op) wires ih using 1
    congr
    funext j
    exact Fin.elim0 j
  | gamma extra choice live i o wires childSigs _ _ ihChildren ihRest =>
    exact .gamma extra choice live i o wires childSigs ihChildren ihRest
  | theta live i wires bodySigs _ _ ihChildren ihRest =>
    exact .theta live i wires bodySigs ihChildren ihRest

theorem erase_eq_mapTerm {t : Term (WireOp A) (Threaded args) past sigs (Threaded outs)}
    (h : Checked A.base.pure A.base.effect a b live t) :
    h.erase = Institution.mapTerm (eraseOpcode A) t := by
  induction h with
  | ret => rfl
  | primitive live i o op wires _ ih =>
    simp only [Checked.erase, Institution.mapTerm, Node.ofBase, OrderedRuntime.Structured.primitiveNode,
      eraseOpcode, ih]
    congr
    funext j
    exact Fin.elim0 j
  | gamma extra choice live i o wires childSigs _ _ ihChildren ihRest =>
    simp only [Checked.erase, Institution.mapTerm, ihChildren, ihRest]
  | theta live i wires bodySigs _ _ ihChildren ihRest =>
    simp only [Checked.erase, Institution.mapTerm, ihChildren, ihRest]
    rfl

variable {P Q : Dialect.{u,v} V PUnit.{u+1}}

private theorem threaded_heq (f : OpcodeMap P Q)
    (hf : ∀ ins outs, Function.Injective (@f ins outs))
    {i o i' o' : Ports (Ty V)} (x : ThreadedOp P i o) (y : ThreadedOp P i' o')
    (hi : i = i') (ho : o = o') (h : HEq (mapThreadedOpcode f x) (mapThreadedOpcode f y)) :
    HEq x y := by
  cases x with
  | @op ins outs op =>
    cases y with
    | @op ins' outs' op' =>
      have ei : ins = ins' := List.append_cancel_right hi
      have eo : outs = outs' := List.append_cancel_right ho
      subst ins'
      subst outs'
      have equal : ThreadedOp.op (f op) = ThreadedOp.op (f op') := eq_of_heq h
      cases hf ins outs (ThreadedOp.op.inj equal)
      rfl

theorem threaded_injective (f : OpcodeMap P Q) (hf : ∀ ins outs, Function.Injective (@f ins outs)) :
    ∀ ins outs, Function.Injective (@mapThreadedOpcode V P Q f ins outs) :=
  fun _ _ _ _ h => eq_of_heq (threaded_heq f hf _ _ rfl rfl (heq_of_eq h))

theorem mapGraph_id (g : Graph (WireOp A) args past sigs outs) : mapGraph (𝟙 A) g = g := by
  have ops : @wireOpcodeMap _ _ _ (𝟙 A) = (fun _ _ op => op) := by
    funext ins outs op
    cases op with | ordered _ _ op => cases op <;> rfl
  simp only [mapGraph, ops, Institution.mapGraph_id]

theorem mapGraph_comp (f : A ⟶ B) (g : B ⟶ C) (t : Graph (WireOp A) args past sigs outs) :
    mapGraph (f ≫ g) t = mapGraph g (mapGraph f t) := by
  have ops : @wireOpcodeMap _ _ _ (f ≫ g) =
      (fun _ _ op => wireOpcodeMap g (wireOpcodeMap f op)) := by
    funext ins outs op
    cases op with | ordered _ _ op => cases op <;> rfl
  simp only [mapGraph, ops, Institution.mapGraph_comp]

theorem eraseGraph_map (f : A ⟶ B) (g : Graph (WireOp A) args past sigs outs) :
    eraseGraph (mapGraph f g) = Institution.mapGraph (Institution.Signature.opcodeMap (erasedBaseHom f))
      (eraseGraph g) := by
  unfold eraseGraph mapGraph
  rw [← Institution.mapGraph_comp, ← Institution.mapGraph_comp]
  congr 1
  funext ins outs op
  cases op with | ordered _ _ op => cases op <;> rfl

end Silmaril.SSA.RVSDG.NestedTheta.Institution.Wires.Proofs
