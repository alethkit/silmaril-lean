module

public import Silmaril.SSA.Isotope.Bridge.Thms
public import Silmaril.SSA.Thesis.Categorical.Thms

/-! # Soundness of translated LetIter equations in thesis categorical models -/

public section

universe v₁ v₂ u₁ u₂ u v w r

namespace Silmaril.Isotope.Bridge

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [Silmaril.TypeFormers τ] [Silmaril.Thesis.LambdaIter.TypeFormers τ]
  [Silmaril.Thesis.LambdaIter.Subtyping τ]
  {ν : Type w} [DecidableEq ν]
  {Φ : Type v} [Silmaril.HasTy Φ τ] [Silmaril.Thesis.LambdaIter.HasTy Φ τ]
  {ε : Type r} [Silmaril.HasEff Φ ε] [Silmaril.Thesis.LambdaIter.HasEff Φ ε]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : Silmaril.Thesis.LambdaIter.Subtyping.Semantics.Categorical.TypeModel τ V)
  [Silmaril.Thesis.LambdaIter.Subtyping.Semantics.Categorical.InstructionModel J M Φ]

/-- An exact LetIter equation gives equal arrows for its translations in every
thesis categorical model satisfying typing coherence and the model laws. -/
theorem toThesis_categorical_sound (pureEff : ε)
    [Silmaril.Thesis.LambdaIter.LocallyNameless.Categorical.TypingCoherent (ν := ν) (Φ := Φ) J M]
    [Silmaril.Thesis.LambdaIter.LocallyNameless.Categorical.LawfulModel (ν := ν) (Φ := Φ) (pureEff := pureEff) J M]
    (hT : TypeCompat τ) (hI : InstrCompat Φ τ) (hE : EffCompat Φ ε)
    {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {a b : Silmaril.Isotope.LetIter.LocallyNameless.Tm ν Φ n} {A : τ}
    (e : Silmaril.Isotope.LetIter.LocallyNameless.Equiv pureEff Γ β a b A)
    (da : Silmaril.Thesis.LambdaIter.LocallyNameless.HasType Φ (Ctx.toThesis Γ) (BoundCtx.toThesis β) (toThesis a) A)
    (db : Silmaril.Thesis.LambdaIter.LocallyNameless.HasType Φ (Ctx.toThesis Γ) (BoundCtx.toThesis β) (toThesis b) A) :
    Silmaril.Thesis.LambdaIter.LocallyNameless.Categorical.denote J M da = Silmaril.Thesis.LambdaIter.LocallyNameless.Categorical.denote J M db :=
  Silmaril.Thesis.LambdaIter.LocallyNameless.Categorical.sound_between J M ((equiv_iff hT hI hE pureEff).mp e) da db

end Silmaril.Isotope.Bridge
