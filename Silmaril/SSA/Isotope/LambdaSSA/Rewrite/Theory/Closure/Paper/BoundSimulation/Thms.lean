module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Soundness.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation

/-! # Denotational soundness of the let-bound simulation equation

The companion's `Uniform.uniform` permits bottom-effect terms as state changes.
The premise here uses a bound return and its value-map denotation. The
conclusion is equality in a model of the Paper relation.
-/

public section

universe v₁ v₂ u₁ u₂ u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open scoped MonoidalCategory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {L : LCtx τ} {A D : τ}

theorem boundLocalMap_typed {t : Tm Φ} (ht : Tm.HasType (A :: Γ) t D) :
    LSubst.HasType Γ (A :: L) (D :: L) (boundLocalMap t) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.boundLocalMap_typed ht

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

/-- A typed let-bound simulation square preserves the denotation of the
one-block loop when the state expression denotes a value map. Shared tensor
comparisons are used for continuation transport through nested CFGs. -/
theorem sound_bound_simulation
    (shared : ∀ E S : V, ∃ h : J.obj E ⊗ J.obj S = J.obj (E ⊗ S),
      Functor.StrongPremonoidal.tensorIso (J := J) E S = eqToIso h)
    {β p q : Region Φ} {t : Tm Φ}
    (hβ : ValueBranches Γ β (A :: L))
    (hp : ValueBranches (A :: Γ) p (A :: L))
    (hq : Region.HasType (D :: Γ) q (D :: L))
    {ht : Tm.HasType (A :: Γ) t D} {h : ctxObj M (A :: Γ) ⟶ M.obj D}
    (dt : Denotes J M ht (J.map h))
    (square : Paper.Eqv (A :: Γ)
      (p.lsubst (liftLSubstVars (boundLocalMap t)))
      ((Region.br 0 t).bindBranchArguments.lsubst (liftLSubstVars (fun _ => q))) (D :: L)) :
    denoteRegion J M (.cfg (fun _ : Fin 1 => A) hβ.hasType (fun _ => hp.hasType)) =
    denoteRegion J M (.cfg (fun _ : Fin 1 => D) (hβ.hasType.lsubst (boundLocalMap_typed ht))
      (fun _ => hq)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.sound_bound_simulation J M shared hβ hp hq dt square

/-- A semantic equality for the two exactly typed bound local compositions
suffices to compare the CFG denotations under the value-map witness. -/
theorem sound_bound_simulation_of_denotations
    (shared : ∀ E S : V, ∃ h : J.obj E ⊗ J.obj S = J.obj (E ⊗ S),
      Functor.StrongPremonoidal.tensorIso (J := J) E S = eqToIso h)
    {β p q : Region Φ} {t : Tm Φ}
    (hβ : ValueBranches Γ β (A :: L))
    (hp : ValueBranches (A :: Γ) p (A :: L))
    (hq : Region.HasType (D :: Γ) q (D :: L))
    {ht : Tm.HasType (A :: Γ) t D} {h : ctxObj M (A :: Γ) ⟶ M.obj D}
    (dt : Denotes J M ht (J.map h))
    (square : ∀ (hl : HasType (A :: Γ)
      (p.lsubst (liftLSubstVars (boundLocalMap t))) (D :: L))
      (hr : HasType (A :: Γ)
        ((Region.br 0 t).bindBranchArguments.lsubst (liftLSubstVars (fun _ => q))) (D :: L)),
      denoteRegion J M hl = denoteRegion J M hr) :
    denoteRegion J M (.cfg (fun _ : Fin 1 => A) hβ.hasType (fun _ => hp.hasType)) =
    denoteRegion J M (.cfg (fun _ : Fin 1 => D) (hβ.hasType.lsubst (boundLocalMap_typed ht))
      (fun _ => hq)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.sound_bound_simulation_of_denotations
    J M shared hβ hp hq dt square

end Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation
