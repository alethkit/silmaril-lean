module

public import Silmaril.SSA.Isotope.LetIter.AbortSequence.Intrinsic.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Kleisli.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Model.Validity.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Model.LocallySmallValidity.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Model.NamedValidity.Thms

/-! # Denotational comparisons for the intrinsic abort-sequencing quotient -/

public section

namespace Silmaril.Isotope.LetIter.LocallyNameless.Intrinsic

open CategoryTheory CategoryTheory.Limits Silmaril.Elgot
open Silmaril.Isotope.LetIter.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
open scoped MonoidalCategory

universe u v w r u₁ u₂ v₁ v₂

section Soundness

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ν : Type w} [DecidableEq ν] {ε : Type r} [HasEff Φ ε]
  [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {A : τ} {e pe : ε}
  {a b : Term Φ Γ β A e}

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V) [InstructionModel J M Φ]

/-- Class equality gives equality of denotations in coherent strong Elgot Freyd
models with a central unit and equality-induced tensor comparison. -/
theorem denote_eq_of_abortClass_eq
    (coherent : TypingCoherent (ν := ν) J M Φ)
    (shared : ∀ R S : V, ∃ h : J.obj R ⊗ J.obj S = J.obj (R ⊗ S),
      Functor.StrongPremonoidal.tensorIso (J := J) R S = eqToIso h)
    (pureInstr : ∀ f : Φ, IsPure pe f → ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
      InstructionModel.denote (J := J) (M := M) f = J.map p)
    (da : Derivation Φ Γ β a.val A) (db : Derivation Φ Γ β b.val A)
    (h : abortClass pe a = abortClass pe b) :
    denote J M da = denote J M db :=
  denote_abortEquiv_of_coherent_shared_tensor J M coherent shared pureInstr
    (abortClass_eq_iff.mp h) da db

end Soundness

section Kleisli

variable {α : Type u} [DecidableEq α] (F : α → Type (max u v))
  {m : Type (max u v) → Type (max u v)} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  {Φ : Type u₁} [HasTy Φ (Ty α)] (M : Isotope.Semantics.InstructionModel (Ty.denote F) Φ m)
  {ν : Type w} [DecidableEq ν] {ε : Type r} [HasEff Φ ε]
  [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  {Γ : Ctx ν (Ty α)} {n : Nat} {β : BoundCtx (Ty α) n} {A : Ty α} {e : ε}
  {a b : Term Φ Γ β A e}

/-- The set-valued lawful Elgot monad model respects class equality at the
bottom purity test if bottom-effect primitives are interpreted by pure maps. -/
theorem denoteOfType_eq_of_abortClass_eq
    (pureM : Isotope.Semantics.InstructionModel.RespectsPure (ε := ε) M)
    (da : Derivation Φ Γ β a.val A) (db : Derivation Φ Γ β b.val A)
    (h : abortClass (⊥ : ε) a = abortClass (⊥ : ε) b) :
    denoteOfType (Ty.denote F) M da = denoteOfType (Ty.denote F) M db :=
  denoteOfType_eq_of_abortEquiv F M pureM (abortClass_eq_iff.mp h) da db

end Kleisli

section EmptyFreeContext

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]
  [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  {n : Nat} {β : BoundCtx τ n} {A : τ} {e : ε} (pe : ε)
  {a b : Term Φ (Ctx.nil : Ctx Empty τ) β A e}

/-- The repaired syntactic strong Elgot Freyd model separates distinct
intrinsic classes at the empty free context. -/
theorem abortClass_eq_iff_repairedDenoteInSyntax_eq
    (da : Derivation Φ (Ctx.nil : Ctx Empty τ) β a.val A)
    (db : Derivation Φ (Ctx.nil : Ctx Empty τ) β b.val A) :
    abortClass pe a = abortClass pe b ↔ repairedDenoteInSyntax pe da = repairedDenoteInSyntax pe db :=
  abortClass_eq_iff.trans (repairedDenoteInSyntax_eq_iff pe da db).symm

/-- Class equality coincides with validity in the coherent shared-tensor
class at the signature universe, for an empty free context. -/
theorem abortClass_eq_iff_repairedCategoricalValidity
    (da : Derivation Φ (Ctx.nil : Ctx Empty τ) β a.val A)
    (db : Derivation Φ (Ctx.nil : Ctx Empty τ) β b.val A) :
    abortClass pe a = abortClass pe b ↔ RepairedCategoricalValidity pe da db :=
  abortClass_eq_iff.trans (abortEquiv_iff_repairedCategoricalValidity pe da db)

end EmptyFreeContext

section LocallySmall

variable {τ Φ ε : Type} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]
  [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  {n : Nat} {β : BoundCtx τ n} {A : τ} {e : ε} (pe : ε)

/-- For a small signature and empty free context, class equality coincides with
validity in the coherent shared-tensor class with `Type 1` objects and small homs. -/
theorem abortClass_eq_iff_repairedLocallySmallValidity
    {a b : Term Φ (Ctx.nil : Ctx Empty τ) β A e}
    (da : Derivation Φ (Ctx.nil : Ctx Empty τ) β a.val A)
    (db : Derivation Φ (Ctx.nil : Ctx Empty τ) β b.val A) :
    abortClass pe a = abortClass pe b ↔ RepairedLocallySmallValidity pe da db :=
  abortClass_eq_iff.trans (abortEquiv_iff_repairedLocallySmallValidity pe da db)

/-- The split-universe characterization extends to named contexts whose
native lookup reaches every free slot. -/
theorem abortClass_eq_iff_repairedNamedLocallySmallValidity
    {ν : Type w} [DecidableEq ν] {Γ : Ctx ν τ} (visible : NamedContext.AllSlotsVisible Γ)
    {a b : Term Φ Γ β A e}
    (da : Derivation Φ Γ β a.val A) (db : Derivation Φ Γ β b.val A) :
    abortClass pe a = abortClass pe b ↔ RepairedNamedLocallySmallValidity pe da db :=
  abortClass_eq_iff.trans (abortEquiv_iff_repairedNamedLocallySmallValidity pe visible da db)

end LocallySmall

end Silmaril.Isotope.LetIter.LocallyNameless.Intrinsic
