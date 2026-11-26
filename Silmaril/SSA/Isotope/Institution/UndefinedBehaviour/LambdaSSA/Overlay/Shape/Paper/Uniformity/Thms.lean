module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Thms
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Uniformity.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Substitution.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Uniformity.Forwarding
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Uniformity.Interpretation

/-! # Observational soundness of guarded Paper uniformity -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper

open Silmaril.DeBruijn (lift)
open LambdaSSA.Region (liftLSubstVars SubstitutionEquiv ValueBranches)
open LambdaSSA.Region.CfgEta.Uniformity (localMap)
open LambdaSSA.Tm (BranchValue)
open LambdaSSA.Semantics (Env extend)

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

variable {entry p : LambdaSSA.Region Φ}

section Forwarding
variable {K : List (Ty κ)} {r : LambdaSSA.Region Φ} {k : Nat → LambdaSSA.Region Φ}
  {α : Type w} {σ : Type x} {env : Env α}
  {instr : Φ → Value α → σ → Value α → σ → Prop}

/-- A whole guarded producer forwards each successful exit exactly at the
producer's final machine state. Nested CFG labels remain local. -/
theorem guarded_forwarding_eval (hr : ValueBranches Γ r L) (hk : LambdaSSA.Region.LSubst.Forwards Γ L K k)
    {s t : σ} {j : Nat} {b : Value α} :
    Semantics.Region.Eval instr env (r.lsubst k) s j b t ↔
      ∃ i a, Semantics.Region.Eval instr env r s i a t ∧
        Semantics.Region.Eval instr (extend env a) (k i) t j b t :=
  (Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Uniformity.forwarding hr hk
    ⟨instr, fun _ _ _ _ => False, fun _ _ _ => False⟩ env).eval

theorem guarded_forwarding_fault (hr : ValueBranches Γ r L) (hk : LambdaSSA.Region.LSubst.Forwards Γ L K k)
    {faults : Φ → Value α → σ → σ → Prop} {s t : σ} :
    Semantics.Region.Fault instr faults env (r.lsubst k) s t ↔
      Semantics.Region.Fault instr faults env r s t :=
  (Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Uniformity.forwarding hr hk
    ⟨instr, faults, fun _ _ _ => False⟩ env).fault

/-- Forwarding preserves divergence for arbitrary primitive divergence
relations, including internal replay when the primitive relation is empty. -/
theorem guarded_forwarding_diverges
    (hr : ValueBranches Γ r L) (hk : LambdaSSA.Region.LSubst.Forwards Γ L K k)
    {prim : Φ → Value α → σ → Prop} {s : σ} :
    Semantics.External.Diverges instr prim (.region env (r.lsubst k) s) ↔
      Semantics.External.Diverges instr prim (.region env r s) :=
  (Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Uniformity.forwarding hr hk
    ⟨instr, fun _ _ _ _ => False, prim⟩ env).div

end Forwarding

/-- The installed Paper uniformity generator preserves shaped UB observations
once its exact literal square has been interpreted. Both simulations match
the chosen successor with its machine state. Faults, primitive divergence
and internal replay are preserved and reflected. -/
theorem uniform_of_observed_square
    (he : ValueBranches Γ entry (A :: L)) (hp : ValueBranches (A :: Γ) p (A :: L))
    (hq : q.HasType (D :: Γ) (D :: L)) (ha : BranchValue (A :: Γ) a D)
    (square : ∀ (M : Shape.Model.{u,v,w,x} Φ (A :: Γ)) (s : M.raw.σ),
      Shape.denote (.native (squareLeft hp ha)) M s = Shape.denote (.native (squareRight hq ha)) M s)
    (M : Shape.Model.{u,v,w,x} Φ Γ) (s : M.raw.σ) :
    Shape.denote (.native (uniformSource he hp)) M s =
      Shape.denote (.native (uniformTarget he hq ha)) M s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Uniformity.uniform_of_observed_square he hp hq ha square M s

/-- The native-square subcase of Paper uniformity. Its square is proved
by the installed native substitution rules, whose shaped soundness supplies
the observational premise. -/
theorem uniform_native_square
    (he : ValueBranches Γ entry (A :: L)) (hp : ValueBranches (A :: Γ) p (A :: L))
    (hq : q.HasType (D :: Γ) (D :: L)) (ha : BranchValue (A :: Γ) a D)
    (square : SubstitutionEquiv (A :: Γ) (squareLeft hp ha).val (squareRight hq ha).val (D :: L))
    (M : Shape.Model.{u,v,w,x} Φ Γ) (s : M.raw.σ) :
    Shape.denote (.native (uniformSource he hp)) M s =
      Shape.denote (.native (uniformTarget he hq ha)) M s :=
  uniform_of_observed_square he hp hq ha (Shape.Continuation.substitutionEquiv_denote square) M s

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper
