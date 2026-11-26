module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Defs

/-! # Literal constructor branches of the guarded Paper simulation square -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper

open Silmaril.DeBruijn (lift)
open LambdaSSA.Region (liftLSubstVars SubstitutionEquiv)
open LambdaSSA.Region.CfgEta.Uniformity (localMap)
open LambdaSSA.Tm (BranchValue)

universe u v w x

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)] {Γ L : List (Ty κ)}
  {A D : Ty κ} {a b : Tm Φ} {q : LambdaSSA.Region Φ}

/-- On the right of the installed simulation square, the literal substitution
agrees with binding the constructor value before running `q`. Effects in
`q`, including CFG replay, retain their observations. -/
theorem uniform_square_right (ha : BranchValue (A :: Γ) a D) (hq : q.HasType (D :: Γ) (D :: L))
    (M : Shape.Model.{u,v,w,x} Φ (A :: Γ)) (s : M.raw.σ) :
    Shape.denote (.native ⟨(.br 0 a : LambdaSSA.Region Φ).lsubst (liftLSubstVars (fun _ => q)),
      ((SubstitutionEquiv.letValue ha (hq.renameVars ((Ren.wk Γ A).lift D))).typed.2)⟩) M s =
    Shape.denote (.native ⟨.let₁ a (q.renameVars (lift Nat.succ)),
      .let₁ ha.hasType (hq.renameVars ((Ren.wk Γ A).lift D))⟩) M s :=
  (Shape.Continuation.substitutionEquiv_denote
    (SubstitutionEquiv.letValue ha (hq.renameVars ((Ren.wk Γ A).lift D))) M s).symm

/-- A local constructor branch on the left of the square first binds its
payload, then computes the constructor state map in the old capture. -/
theorem uniform_square_left_branch (ha : BranchValue (A :: Γ) a D) (hb : BranchValue (A :: Γ) b A)
    (M : Shape.Model.{u,v,w,x} Φ (A :: Γ)) (s : M.raw.σ) :
    let mapped : (a.rename (lift Nat.succ)).HasType (A :: A :: Γ) D :=
      ha.hasType.rename ((Ren.wk Γ A).lift A)
    let body : (LambdaSSA.Region.br 0 (a.rename (lift Nat.succ))).HasType (A :: A :: Γ) (D :: L) :=
      .br (ℓ := 0) rfl mapped
    Shape.denote (.native ⟨(.br 0 b : LambdaSSA.Region Φ).lsubst (liftLSubstVars (localMap a)),
      (SubstitutionEquiv.letValue hb body).typed.2⟩) M s =
    Shape.denote (.native ⟨.let₁ b (.br 0 (a.rename (lift Nat.succ))), .let₁ hb.hasType body⟩) M s := by
  dsimp only
  exact (Shape.Continuation.substitutionEquiv_denote (SubstitutionEquiv.letValue hb
    (.br (L := D :: L) (ℓ := 0) rfl (ha.hasType.rename ((Ren.wk Γ A).lift A)))) M s).symm

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper
