module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Coproducts.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Singleton.Thms

/-! # Coproducts in the CFG η quotient -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.CfgEta

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}

def emptyIsInitial : IsInitial ((fromNative (Φ := Φ) (Γ := Γ)).obj ContinuationContext.empty) :=
  IsInitial.ofUniqueHom
    (fun Z => toHom (X := fromNative.obj ContinuationContext.empty) (Y := Z)
      ⟨labelId, fun i _ hi => (Nat.not_lt_zero i (List.getElem?_eq_some_iff.mp hi).1).elim⟩)
    (fun _ f => Quotient.inductionOn f (fun _ => toHom_eq_iff.mpr
      (fun i _ hi => (Nat.not_lt_zero i (List.getElem?_eq_some_iff.mp hi).1).elim)))

private theorem append_hom_ext (X Y : ContinuationContext Φ Γ) {Z : Interface Φ Γ}
    {f g : fromNative.obj (X.append Y) ⟶ Z}
    (hl : fromNative.map (X.appendInl Y) ≫ f = fromNative.map (X.appendInl Y) ≫ g)
    (hr : fromNative.map (X.appendInr Y) ≫ f = fromNative.map (X.appendInr Y) ≫ g) :
    f = g := by
  obtain ⟨σ, rfl⟩ := Quotient.exists_rep f
  obtain ⟨υ, rfl⟩ := Quotient.exists_rep g
  have left := toHom_eq_iff.mp hl
  have right := toHom_eq_iff.mp hr
  apply toHom_eq_iff.mpr
  intro i A hi
  change At (X.labels ++ Y.labels) i A at hi
  by_cases h : i < X.labels.length
  · rw [At, List.getElem?_append_left h] at hi
    have he := left hi
    change Eqv (A :: Γ) (compLSubst labelId σ.val i)
      (compLSubst labelId υ.val i) Z.labels at he
    simpa only [compLSubst_id_left] using he
  · have hle := Nat.le_of_not_gt h
    rw [At, List.getElem?_append_right hle] at hi
    have he := right hi
    change Eqv (A :: Γ) (compLSubst labelId σ.val (X.labels.length + (i - X.labels.length)))
      (compLSubst labelId υ.val (X.labels.length + (i - X.labels.length))) Z.labels at he
    simpa only [compLSubst_id_left, Nat.add_sub_of_le hle] using he

noncomputable def appendIsColimit (X Y : ContinuationContext Φ Γ) :
    IsColimit (BinaryCofan.mk (fromNative.map (X.appendInl Y)) (fromNative.map (X.appendInr Y))) := by
  let colim := X.appendIsColimit Y
  let F := fromNative (Φ := Φ) (Γ := Γ)
  let liftObj (Z : Interface Φ Γ) : ContinuationContext Φ Γ := ⟨Z.labels⟩
  let s {Z : Interface Φ Γ} (f : F.obj X ⟶ Z) (g : F.obj Y ⟶ Z) :=
    BinaryCofan.mk (F.preimage (Y := liftObj Z) f) (F.preimage (Y := liftObj Z) g)
  let desc {Z : Interface Φ Γ} (f : F.obj X ⟶ Z) (g : F.obj Y ⟶ Z) :=
    F.map (colim.desc (s f g))
  have facLeft {Z : Interface Φ Γ} (f : F.obj X ⟶ Z) (g : F.obj Y ⟶ Z) :
      F.map (X.appendInl Y) ≫ desc f g = f := by
    have h : X.appendInl Y ≫ colim.desc (s f g) = F.preimage (Y := liftObj Z) f :=
      colim.fac (s f g) ⟨.left⟩
    exact (F.map_comp _ _).symm.trans
      ((congrArg F.map h).trans (F.map_preimage (X := X) (Y := liftObj Z) f))
  have facRight {Z : Interface Φ Γ} (f : F.obj X ⟶ Z) (g : F.obj Y ⟶ Z) :
      F.map (X.appendInr Y) ≫ desc f g = g := by
    have h : X.appendInr Y ≫ colim.desc (s f g) = F.preimage (Y := liftObj Z) g :=
      colim.fac (s f g) ⟨.right⟩
    exact (F.map_comp _ _).symm.trans
      ((congrArg F.map h).trans (F.map_preimage (X := Y) (Y := liftObj Z) g))
  exact BinaryCofan.IsColimit.mk _ desc (fun {_} => facLeft) (fun {_} => facRight)
    (fun {_} f g _ hf hg => append_hom_ext X Y (hf.trans (facLeft f g).symm)
      (hg.trans (facRight f g).symm))

noncomputable def singletonSumIsColimit (A B : τ) :
    let X : ContinuationContext Φ Γ := ContinuationContext.single A
    let Y : ContinuationContext Φ Γ := ContinuationContext.single B
    IsColimit (BinaryCofan.mk
      (fromNative.map (X.appendInl Y ≫ ContinuationContext.sumTag A B))
      (fromNative.map (X.appendInr Y ≫ ContinuationContext.sumTag A B))) := by
  dsimp only
  let F := fromNative (Φ := Φ) (Γ := Γ)
  let nativeAppend := (ContinuationContext.single (Φ := Φ) (Γ := Γ) A).appendIsColimit
    (ContinuationContext.single B)
  let nativeSum := ContinuationContext.singletonSumIsColimit (Φ := Φ) (Γ := Γ) A B
  refine IsColimit.ofIsoColimit (appendIsColimit _ _)
    (Cocone.ext (F.mapIso (nativeAppend.coconePointUniqueUpToIso nativeSum)) ?_)
  rintro ⟨_ | _⟩
  · exact (F.map_comp _ _).symm.trans
      (congrArg F.map (nativeAppend.comp_coconePointUniqueUpToIso_hom nativeSum ⟨.left⟩))
  · exact (F.map_comp _ _).symm.trans
      (congrArg F.map (nativeAppend.comp_coconePointUniqueUpToIso_hom nativeSum ⟨.right⟩))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta
