module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.InstructionFree.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Thms

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.InstructionFreeSimulation

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

theorem valueBranches {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (e : InstructionFreeStep Γ r s L) : ValueBranches Γ r L ∧ ValueBranches Γ s L := by
  cases e with
  | @simulate Γ A D entry p q t he hp hq ht pure square =>
    have maps : LSubst.ValueFamily Γ (A :: L) (D :: L) (boundLocalMap t) := by
      intro i T hi
      cases i with
      | zero =>
        cases Option.some.inj hi
        exact (Region.HasType.br (ℓ := 0) (show At (D :: L) 0 D from rfl) ht).bindBranchArguments
      | succ i => exact .br (ℓ := i + 1) hi (.var (i := 0) rfl)
    exact ⟨.cfg (fun _ : Fin 1 => A) he (fun _ => hp),
      .cfg (fun _ : Fin 1 => D) (he.lsubst maps) (fun _ => hq)⟩

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open scoped MonoidalCategory

universe u₁ u₂ v₁ v₂

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

theorem denotes
    (shared : ∀ E S : V, ∃ h : J.obj E ⊗ J.obj S = J.obj (E ⊗ S),
      Functor.StrongPremonoidal.tensorIso (J := J) E S = eqToIso h)
    {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (e : InstructionFreeStep Γ r s L)
    (hr : HasType Γ r L) (hs : HasType Γ s L) :
    ∃ f, RegionDenotes J M hr f ∧ RegionDenotes J M hs f := by
  cases e with
  | @simulate Γ A D entry p q t he hp hq ht pure square =>
    let : HasEff Φ Bool := ⟨fun _ => true⟩
    have noPurePrimitive (f : Φ) :
        ¬ @IsPure Φ Bool ⟨fun _ => true⟩ false f := Bool.noConfusion
    obtain ⟨_, dt⟩ := pure.denotes_map J M ht (fun f hf => (noPurePrimitive f hf).elim)
    have eq := sound_bound_simulation J M shared he hp hq.hasType dt square
    let hleft := HasType.cfg (fun _ : Fin 1 => A) he.hasType (fun _ => hp.hasType)
    let hright := HasType.cfg (fun _ : Fin 1 => D) (he.hasType.lsubst (boundLocalMap_typed ht))
      (fun _ => hq.hasType)
    change denoteRegion J M hleft = denoteRegion J M hright at eq
    exact ⟨denoteRegion J M hr, denoteRegion_spec J M hr, eq.symm ▸ denoteRegion_spec J M hs⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.InstructionFreeSimulation
