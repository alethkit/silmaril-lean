module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseAndUnaryReturns.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Generation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseAndUnaryReturnGeneration

/-! # Guarded case and unary return generation -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseAndUnaryReturns

open Silmaril Silmaril.Isotope.LambdaSSA
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper
open CategoryTheory CategoryTheory.Limits
open CfgEta.TypeCategory (returnRegion_typed)
open Paper.Extension.Singleton (ofRegion)
open Paper.Extension.Singleton.Generation (Generated)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open Paper.RetainedLet (unpackBody_typed)
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v w u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

section Returns

variable (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
  (contains : ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ}, Step pe Γ r s L → Seed Γ r s L)

set_option hygiene false in
local notation "Lit" => ofRegion Seed

variable {X A B D : τ} {a b : Tm Φ}

include contains in
/-- A pure case on the singleton sum input is the exact copair of the two returned arms. -/
theorem returnCase_eq_copair (ha : Tm.HasType [A] a D) (hb : Tm.HasType [B] b D)
    (pa : Tm.Pure pe a) (pb : Tm.Pure pe b) :
    Lit (returnRegion_typed (.case (.var (i := 0) rfl)
      (ha.rename ((Ren.wk [] (coprod A B)).lift A)) (hb.rename ((Ren.wk [] (coprod A B)).lift B)))) =
      exactCopair (Seed) (Lit (returnRegion_typed ha)) (Lit (returnRegion_typed hb)) :=
  CaseAndUnaryReturnGeneration.returnCase_eq_copair pe Seed contains ha hb pa pb

include contains in
/-- Unary forwarding fusion exposes the exact returning let, including captures. -/
theorem returnLet_eq_let (ha : Tm.HasType [X] a A) (hb : Tm.HasType [A, X] b D) :
    Lit (returnRegion_typed (.let₁ ha hb)) = Lit (.let₁ ha (returnRegion_typed hb)) :=
  CaseAndUnaryReturnGeneration.returnLet_eq_let pe Seed contains ha hb

include contains in
/-- Generation of the returned scrutinee and the packed body gives generation of the literal unary let. -/
theorem generated_returnLet {r : Region Φ} (ha : Tm.HasType [X] a A)
    (hr : ValueBranches [A, X] r [D]) (g₁ : Generated (Seed) (Lit (returnRegion_typed ha)))
    (g₂ : Generated (Seed) (Lit (unpackBody_typed hr))) :
    Generated (Seed) (Lit (.let₁ ha hr)) :=
  CaseAndUnaryReturnGeneration.generated_returnLet pe Seed contains ha hr g₁ g₂

include contains in
/-- Generation of the two packed constituents suffices for a retained returning let. -/
theorem generated_retained_returnLet (ha : Tm.HasType [X] a A) (hb : Tm.HasType [A, X] b D)
    (g₁ : Generated (Seed) (Lit (returnRegion_typed ha)))
    (g₂ : Generated (Seed) (Lit (unpackBody_typed (returnRegion_typed hb)))) :
    Generated (Seed) (Lit (returnRegion_typed (.let₁ ha hb))) :=
  CaseAndUnaryReturnGeneration.generated_retained_returnLet pe Seed contains ha hb g₁ g₂

/-- With an unused capture the returning let is ordinary composition. -/
theorem returnLet_eq_comp (ha : Tm.HasType [X] a A) (hb : Tm.HasType [A] b D) :
    Lit (returnRegion_typed (.let₁ ha (hb.rename ((Ren.wk [] X).lift A)))) =
      Lit (returnRegion_typed ha) ≫ Lit (returnRegion_typed hb) :=
  CaseAndUnaryReturnGeneration.returnLet_eq_comp Seed ha hb

include contains in
/-- Induction gives generation for the displayed returning terms. -/
theorem generated_returnFragment {t : Tm Φ} {ht : Tm.HasType [X] t D}
    (h : ReturnFragment pe ht) : Generated (Seed) (Lit (returnRegion_typed ht)) :=
  CaseAndUnaryReturnGeneration.generated_returnFragment pe Seed contains h

end Returns

set_option hygiene false in
local notation "Seed" => Step (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "Joined" => JoinedStep (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "Lit" => ofRegion (Seed)

section Soundness

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C] [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

/-- Each seed is sound in the existing coherent shared-tensor model interface. -/
theorem eqv_sound
    (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
      Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)
    {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (e : Paper.Extension.Eqv (Seed) Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs :=
  CaseAndUnaryReturnGeneration.eqv_sound pe J M shared e hr hs

/-- The same denotation comparison holds when projection returns and unit η are included. -/
theorem joined_eqv_sound
    (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
      Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)
    {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (e : Paper.Extension.Eqv (Joined) Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs :=
  CaseAndUnaryReturnGeneration.joined_eqv_sound pe J M shared e hr hs

/-- The guarded singleton comparison preserves exact typed denotation. -/
theorem denoteSingleton_eq_ofRegion_eq
    (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
      Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)
    {A B : τ} {r s : Region Φ} (hr : ValueBranches [A] r [B]) (hs : ValueBranches [A] s [B])
    (e : Lit hr = Lit hs) :
    denoteSingletonRegion J M hr.hasType = denoteSingletonRegion J M hs.hasType :=
  CaseAndUnaryReturnGeneration.denoteSingleton_eq_ofRegion_eq pe J M shared hr hs e

end Soundness

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseAndUnaryReturns
