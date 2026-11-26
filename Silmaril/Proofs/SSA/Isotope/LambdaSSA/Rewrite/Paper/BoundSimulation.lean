module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Soundness.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Uniformity.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Direct.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Assembly.Thms

/-! # Bind-first transport of the pure state simulation equation -/

public section

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical.SingletonDispatcher
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.Uniformity (localMap localMap_typed)
open scoped MonoidalCategory

universe v₁ v₂ u₁ u₂ u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation

open Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation (boundLocalMap)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {L : LCtx τ} {A D : τ}

theorem boundLocalMap_typed {t : Tm Φ} (ht : Tm.HasType (A :: Γ) t D) :
    LSubst.HasType Γ (A :: L) (D :: L) (boundLocalMap t) := by
  intro i T hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    exact (.br (ℓ := 0) (show At (D :: L) 0 D from rfl) ht : HasType _ _ _).bindBranchArguments.hasType
  | succ i => exact .br (ℓ := i + 1) hi (.var (i := 0) rfl)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

private theorem boundLocalMap_denotes {t : Tm Φ}
    {k : J.obj (ctxObj M Γ ⊗ labelObj M (A :: L)) ⟶ J.obj (labelObj M (D :: L))}
    (d : ContinuationDenotes J M (localMap t) k) :
    ContinuationDenotes J M (boundLocalMap t) k := by
  intro i T hi
  obtain ⟨hr, dr⟩ := d hi
  cases i with
  | zero =>
    refine ⟨hr.bindBranchArguments.hasType, ?_⟩
    have e := (RegionDenotes.eq_denote J M dr).trans
      (Region.denoteRegion_bindBranchArguments J M (FreydCategory.CentralUnit.unit_central (J := J)) hr)
    rw [e]
    exact denoteRegion_spec J M _
  | succ i => exact ⟨hr, dr⟩

/-- Soundness of the bound simulation square at a one-block CFG. This checks
a candidate equation without extending the Paper relation. -/
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
      (fun _ => hq)) := by
  have raw := localMap_typed (L := L) ht
  have bound := boundLocalMap_typed (L := L) ht
  let hl := hp.hasType.lsubst (raw.liftVars A)
  let hl' := hp.hasType.lsubst (bound.liftVars A)
  have family : LSubst.HasType Γ [D] (D :: L) (fun _ => q) :=
    fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ hq
  let init : Region.HasType (A :: Γ) (.br 0 t) [D] := .br (ℓ := 0) rfl ht
  let hr := init.lsubst (family.liftVars A)
  let hr' := init.bindBranchArguments.hasType.lsubst (family.liftVars A)
  obtain ⟨_, dl⟩ := ContinuationDenotes.exists_of_typed M J raw
  have dl' := boundLocalMap_denotes J M dl
  -- Normalizing each local continuation preserves its arrow.
  have leftEq :
      denoteRegion J M hl = denoteRegion J M hl' :=
    (denoteRegion_lsubst_sharedTensor J M shared hp.hasType hl
      (PureBranches.of_valueBranches J M hp) (dl.weakenCapture J M A)).trans
    (denoteRegion_lsubst_sharedTensor J M shared hp.hasType hl'
      (PureBranches.of_valueBranches J M hp) (dl'.weakenCapture J M A)).symm
  obtain ⟨_, dr⟩ := ContinuationDenotes.exists_of_typed M J (family.liftVars A)
  -- On the other path, the value-map witness licenses literal substitution.
  have rightEq : denoteRegion J M hr = denoteRegion J M hr' :=
    (denoteRegion_lsubst_sharedTensor J M shared init hr (.br rfl dt) dr).trans
    (denoteRegion_bound_lsubst_sharedTensor J M shared init hr' dr).symm
  have rawSquare := leftEq.trans ((square hl' hr').trans rightEq.symm)
  have hs := CfgEta.Uniformity.sound_entry_of_denotations M J shared hβ hp hq dt hl hr rawSquare
  have entryEq : denoteRegion J M (hβ.hasType.lsubst raw) =
      denoteRegion J M (hβ.hasType.lsubst bound) :=
    (denoteRegion_lsubst_sharedTensor J M shared hβ.hasType _
      (PureBranches.of_valueBranches J M hβ) dl).trans
    (denoteRegion_lsubst_sharedTensor J M shared hβ.hasType _
      (PureBranches.of_valueBranches J M hβ) dl').symm
  refine hs.trans ?_
  rw [denoteSingleCfg M J (hβ.hasType.lsubst raw) hq,
    denoteSingleCfg M J (hβ.hasType.lsubst bound) hq, entryEq]

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
  sound_bound_simulation_of_denotations J M shared hβ hp hq dt
    (Paper.Eqv.sound J M shared square)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation
