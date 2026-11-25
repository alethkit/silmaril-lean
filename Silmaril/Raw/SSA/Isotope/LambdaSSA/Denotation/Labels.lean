module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)

universe u v

variable {V : Type u} [Category.{v} V] [CartesianMonoidalCategory V]
  [HasFiniteCoproducts V] {τ : Type*} [TypeFormers τ] (M : TypeModel τ V)

/-- Expose the transport hidden by `labelInject` before the canonical
coproduct injection.  This form is suitable for reassociation with a
coproduct eliminator. -/
@[reassoc]
theorem labelInject_eq_sigma (M : TypeModel τ V) {L : LCtx τ}
    (i : Nat) {A : τ} (h : At L i A) :
    let hi : i < L.length := (List.getElem?_eq_some_iff.mp h).1
    let j : Fin L.length := ⟨i, hi⟩
    let hj : L.get j = A := (List.getElem?_eq_some_iff.mp h).2
    labelInject M i h =
      eqToHom (congrArg M.obj hj.symm) ≫
        Sigma.ι (fun k : Fin L.length => M.obj (L.get k)) j := by
  rfl

@[reassoc]
theorem labelInject_labelObjToFinite (R : Fin n → τ) (i : Fin n)
    (h : At (List.ofFn R) i.val (R i)) :
    labelInject M i.val h ≫ labelObjToFinite M R = finiteLabelInject M R i := by
  rw [labelInject_eq_sigma_assoc, labelObjToFinite]
  erw [Category.assoc, Limits.Sigma.ι_comp_desc]
  erw [← Category.assoc, eqToHom_trans]
  exact Category.id_comp _

@[reassoc (attr := simp)] theorem labelAppendSplit_ι (R L : LCtx τ)
    (i : Fin (R ++ L).length) :
    Limits.Sigma.ι (fun k : Fin (R ++ L).length => M.obj ((R ++ L).get k)) i ≫
      labelAppendSplit M R L = labelAppendRoute M R L i := by
  rw [labelAppendSplit, Limits.Sigma.ι_comp_desc]

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
