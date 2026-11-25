module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.CategoryIteration

/-! # Categorical fixpoint in the opt-in one-block CFG η presentation -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory

open CategoryTheory CategoryTheory.Limits
open Silmaril.DeBruijn (lift)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}
  {A B C : τ} {r s : Region Φ}

/-- Singleton representatives denote the same quotient arrow exactly when they are CFG η equivalent. -/
theorem ofRegion_eq_iff (hr : ValueBranches (A :: Γ) r [B]) (hs : ValueBranches (A :: Γ) s [B]) :
    ofRegion hr = ofRegion hs ↔ Eqv (A :: Γ) r s [B] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.ofRegion_eq_iff hr hs

theorem ofRegion_identity (A : τ) :
    ofRegion (r := (.br 0 (.var 0) : Region Φ))
      (show ValueBranches (A :: Γ) (.br 0 (.var 0)) [A] from .br rfl (.var rfl)) = 𝟙 (ofType A) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.ofRegion_identity A

theorem exists_region (f : ofType (Φ := Φ) (Γ := Γ) A ⟶ ofType B) :
    ∃ (r : Region Φ) (hr : ValueBranches (A :: Γ) r [B]), ofRegion hr = f :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.exists_region f

/-- Iteration of a representative is the raw one-label CFG. -/
theorem iterateSum_ofRegion (hr : ValueBranches (A :: Γ) r [Silmaril.coprod B A]) :
    iterateSum (ofRegion hr) = ofRegion (SyntacticCategory.iterateRegion_valueBranches hr) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.iterateSum_ofRegion hr

/-- At the singleton sum type the categorical copair is the typed case on its payload. -/
theorem coprod_desc_ofRegion (hr : ValueBranches (A :: Γ) r [C])
    (hs : ValueBranches (B :: Γ) s [C]) :
    (sumIso A B).hom ≫ coprod.desc (ofRegion hr) (ofRegion hs) = ofRegion (caseValueBranches hr hs) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.coprod_desc_ofRegion hr hs

omit [TypeFormers τ] [HasTy Φ τ] in
/-- Sequencing the identity/loop copair under the step's binder gives the literal decoder. -/
theorem returnOrRepeat_lift (A : τ) (p : Region Φ) :
    (Region.case (.var 0) ((Region.br 0 (.var 0)).renameVars (lift Nat.succ))
        ((SyntacticCategory.iterateRegion A p).renameVars (lift Nat.succ))).renameVars
      (lift Nat.succ) = CfgEta.returnOrRepeat A p :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.returnOrRepeat_lift

/-- Substituting the return-or-repeat decoder preserves value branches. -/
theorem unrolled_valueBranches (hp : ValueBranches (A :: Γ) r [Silmaril.coprod B A]) :
    ValueBranches (A :: Γ) (r.lsubst (fun _ => CfgEta.returnOrRepeat A r)) [B] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.unrolled_valueBranches hp

/-- The right side of fixpoint is literal substitution of the return-or-repeat decoder. -/
theorem iterateSum_unfold_rhs (hp : ValueBranches (A :: Γ) r [Silmaril.coprod B A]) :
    ofRegion hp ≫ ((sumIso B A).hom ≫ coprod.desc (𝟙 (ofType B)) (iterateSum (ofRegion hp))) =
      ofRegion (unrolled_valueBranches hp) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.iterateSum_unfold_rhs hp

/-- The named CFG iteration satisfies fixpoint for every arrow into the chosen coproduct. -/
theorem iterate_fixpoint {X Y : TypeCategory Φ Γ} (f : X ⟶ Y ⨿ X) :
    iterate f = f ≫ coprod.desc (𝟙 Y) (iterate f) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.iterate_fixpoint f

end Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory
