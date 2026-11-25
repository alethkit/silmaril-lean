module

public import Silmaril.Raw.SSA.Isotope.LetIter.ProofRelevant.Semantics.Agreement.Combinators

@[expose] public section

open Silmaril.Isotope.LetIter.LocallyNameless (Tm Pure TypedRenaming)

-- Preserve definitional object conversions across the Kleisli embedding.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- Normalize the model instances together with their dependent object types.
set_option backward.dsimp.instances true

namespace Silmaril.Isotope.LetIter.ProofRelevant.Semantics

open CategoryTheory CategoryTheory.Limits Silmaril.Elgot
open Silmaril.Isotope.LetIter.ProofRelevant.LocallyNameless

universe u v w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]

variable [Iterate m] [LawfulElgotMonad m]
variable [InstructionModel Φ τ ε m]

/-- The abstract categorical semantics, specialized to the Kleisli category of the
monadic model, agrees pointwise with the direct monadic semantics. -/
theorem categorical_denote_eq_proof {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} (h : HasType Φ Γ β t A)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    (Categorical.denoteOfType (ε := ε) (m := m) h).of
        (envToCategorical γ ρ) =
      denote (ε := ε) (m := m) h γ ρ := by
  induction h with
  | fv h =>
      simp [Categorical.denoteOfType, Categorical.denote, denote]
      exact congrArg (pure (f := m)) (freeLookup_toCategorical γ ρ _ h)
  | bv =>
      simp [Categorical.denoteOfType, Categorical.denote, denote]
      exact congrArg (pure (f := m)) (boundVar_toCategorical γ ρ _)
  | op ha ih =>
      have hi := ih ρ
      simp only [Categorical.denoteOfType, Categorical.ofTypeModel] at hi
      simp [Categorical.denoteOfType, Categorical.denote, denote,
        Categorical.ofInstructionModel, Categorical.ofTypeModel, joinM,
        bind_map_left]
      exact congrArg (fun x => x >>= InstructionModel.denote ε _) hi
  | let₁ ha hb iha ihb =>
      have hia := iha ρ
      simp only [Categorical.denoteOfType, Categorical.ofTypeModel] at hia
      have hib (a) := ihb (ρ, a)
      simp only [Categorical.denoteOfType, Categorical.ofTypeModel] at hib
      simp [Categorical.denoteOfType, Categorical.denote, denote,
        Categorical.ofTypeModel]
      refine (Categorical.bind_of (m := m) _ _ (envToCategorical γ ρ)).trans ?_
      simp only [Bind.kleisliRight]
      refine congrArg₂ (fun x k => x >>= k) hia ?_
      funext a
      simp [joinM]
      exact hib a
  | unit =>
      simp [Categorical.denoteOfType, Categorical.denote, denote,
        Categorical.ofTypeModel, Kleisli.Adjunction.toKleisli]
  | pair ha hb iha ihb =>
      have hp := Categorical.pair_of (m := m)
        (Categorical.denoteOfType (ε := ε) (m := m) ha)
        (Categorical.denoteOfType (ε := ε) (m := m) hb) (envToCategorical γ ρ)
      simp [Categorical.denoteOfType, Categorical.denote, denote,
        Categorical.ofTypeModel, joinM]
      refine (congrArg (fun x => Functor.map (f := m)
        (TypeModel.productEquiv _ _).symm x) hp).trans ?_
      simp only [Bind.kleisliRight, map_bind, bind_pure_comp, Functor.map_map, iha ρ, ihb ρ]
      rfl
  | @let₂ n β a A B c C ha hc iha ihc =>
      have hia := iha ρ
      simp only [Categorical.denoteOfType, Categorical.ofTypeModel] at hia
      simp [Categorical.denoteOfType, Categorical.denote, denote,
        Categorical.ofTypeModel]
      refine (Categorical.bind_of (m := m) _ _ (envToCategorical γ ρ)).trans ?_
      simp only [Bind.kleisliRight]
      refine congrArg₂ (fun x k => x >>= k) hia ?_
      funext ab
      simp [joinM]
      change (Categorical.denoteOfType (ε := ε) (m := m) hc).of
        (envToCategorical (β := .snoc (.snoc β A) B) γ
          ((ρ, (TypeModel.productEquiv A B ab).1), (TypeModel.productEquiv A B ab).2)) = _
      exact ihc ((ρ, (TypeModel.productEquiv A B ab).1), (TypeModel.productEquiv A B ab).2)
  | inl ha ih =>
      have hi := ih ρ
      simp only [Categorical.denoteOfType, Categorical.ofTypeModel] at hi
      simp [Categorical.denoteOfType, Categorical.denote, denote,
        Categorical.ofTypeModel, joinM, bind_map_left]
      exact hi
  | inr hb ih =>
      have hi := ih ρ
      simp only [Categorical.denoteOfType, Categorical.ofTypeModel] at hi
      simp [Categorical.denoteOfType, Categorical.denote, denote,
        Categorical.ofTypeModel, joinM, bind_map_left]
      exact hi
  | case he hl hr ihe ihl ihr =>
      have hie := ihe ρ
      simp only [Categorical.denoteOfType, Categorical.ofTypeModel] at hie
      have hil (a) := ihl (ρ, a)
      simp only [Categorical.denoteOfType, Categorical.ofTypeModel] at hil
      have hir (b) := ihr (ρ, b)
      simp only [Categorical.denoteOfType, Categorical.ofTypeModel] at hir
      simp [Categorical.denoteOfType, Categorical.denote, denote,
        Categorical.ofTypeModel]
      refine (Categorical.caseWithContext_of (m := m) _ _ _ (envToCategorical γ ρ)).trans ?_
      simp [Bind.kleisliRight, joinM]
      refine congrArg₂ (fun x k => x >>= k) ?_ ?_
      · exact hie
      funext e
      dsimp only [Kleisli.Adjunction.toKleisli] at hil hir ⊢
      cases h : TypeModel.coprodEquiv _ _ e with
      | inl a =>
          exact hil a
      | inr b =>
          exact hir b
  | abort ha ih =>
      have hi := ih ρ
      simp only [Categorical.denoteOfType, Categorical.ofTypeModel] at hi
      simp [Categorical.denoteOfType, Categorical.denote, denote,
        Categorical.abort, Categorical.ofTypeModel,
        joinM, bind_map_left]
      refine congrArg₂ (fun x k => x >>= k) hi ?_
      funext z
      exact Empty.elim (TypeModel.emptyEquiv z)
  | iter ha hb iha ihb =>
      have hia := iha ρ
      simp only [Categorical.denoteOfType, Categorical.ofTypeModel] at hia
      have hib (a) := ihb (ρ, a)
      simp only [Categorical.denoteOfType, Categorical.ofTypeModel] at hib
      simp [Categorical.denoteOfType, Categorical.denote, denote,
        Categorical.ofTypeModel]
      refine (Categorical.bind_of (m := m) _ _ (envToCategorical γ ρ)).trans ?_
      simp only [Bind.kleisliRight]
      refine congrArg₂ (fun x k => x >>= k) hia ?_
      funext a
      simp []
      refine (Categorical.contextualLoop_of (m := m) _ (envToCategorical γ ρ) a).trans ?_
      apply congrArg (fun q => Silmaril.Elgot.iter (m := m) q a)
      funext x
      dsimp only [Categorical.typeJ, Kleisli.Adjunction.toKleisli, ofTypeMonad, ofTypeFunctor] at hib ⊢
      simp [Bind.kleisliRight, joinM]
      exact hib x
  | sub ha hAB ih =>
      have hi := ih ρ
      simp only [Categorical.denoteOfType, Categorical.ofTypeModel] at hi
      simp [Categorical.denoteOfType, Categorical.denote, denote,
        Categorical.ofTypeModel, joinM, bind_map_left, coeSub, bind_pure_comp]
      exact congrArg (Functor.map (f := m) (TypeModel.coe hAB)) hi

end Silmaril.Isotope.LetIter.ProofRelevant.Semantics

public section

namespace Silmaril.Isotope.LetIter.ProofRelevant.Semantics

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w}

private theorem ctxToCategorical_surjective (Γ : Ctx ν τ) :
    Function.Surjective (ctxToCategorical (Γ := Γ)) := by
  induction Γ with
  | nil =>
    intro x
    refine ⟨PUnit.unit, ?_⟩
    change (PUnit.unit : PUnit.{v + 1}) = x
    cases x
    rfl
  | snoc Γ x A ih =>
    rintro ⟨γ, a⟩
    obtain ⟨input, rfl⟩ := ih γ
    exact ⟨(input, a), rfl⟩

private theorem boundToCategorical_surjective {n : Nat} (β : BoundCtx τ n) :
    Function.Surjective (boundToCategorical (β := β)) := by
  induction β with
  | nil =>
    intro x
    refine ⟨PUnit.unit, ?_⟩
    change (PUnit.unit : PUnit.{v + 1}) = x
    cases x
    rfl
  | snoc β A ih =>
    rintro ⟨ρ, a⟩
    obtain ⟨input, rfl⟩ := ih ρ
    exact ⟨(input, a), rfl⟩

theorem envToCategorical_surjective_proof {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    (input : Categorical.envObj (Categorical.ofTypeModel (τ := τ)) Γ β) :
    ∃ (γ : CtxDen Γ) (ρ : BoundDen β), envToCategorical γ ρ = input := by
  obtain ⟨γ, ρ⟩ := input
  obtain ⟨γ', rfl⟩ := ctxToCategorical_surjective Γ γ
  obtain ⟨ρ', rfl⟩ := boundToCategorical_surjective β ρ
  exact ⟨γ', ρ', rfl⟩

end Silmaril.Isotope.LetIter.ProofRelevant.Semantics
