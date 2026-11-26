module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Expansion.TypeChange.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.TypeChange.Comparison.Thms

/-! # Exact LetCase equations on the validated model class -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution (Room)
open Morphism (SignatureMap)

variable {τ υ ε δ : Type} [TypeFormers τ] [TypeFormers υ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ}
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)

/-- Retain the actual LetCase reduct and the type model that presents it. -/
noncomputable def CoherentRegionModel.validate (K : CoherentRegionModel J P) :
    ValidatedCaseAlgebra J P :=
  ValidatedCaseAlgebra.ofPresentation K K.caseAlgebra rfl

/-- Keep all exact LetCase equations and evaluate them in the underlying
algebras of the validated models. Model morphisms come from equality of
the chosen presentations, as in the SSA room. -/
noncomputable def validatedRoom (P : InstrSig τ ε) : Room.{0, 0, 1} where
  Sen := CaseEquation P
  Mod := Cat.of (ShrinkHoms (Discrete (ValidatedCaseAlgebra J P)))
  Sat A e := ((LetCase.inst Γ₀).obj P).Sat A.fromShrinkHoms.as.algebra e

instance (P : InstrSig τ ε) : IsDiscrete (validatedRoom J P).Mod where
  subsingleton _ _ :=
    (ShrinkHoms.inverse.{0} (Discrete (ValidatedCaseAlgebra J P))).map_injective.subsingleton
  eq_of_hom f :=
    congrArg (ShrinkHoms.toShrinkHoms ∘ Discrete.mk)
      (Discrete.eq_of_hom ((ShrinkHoms.inverse.{0} (Discrete (ValidatedCaseAlgebra J P))).map f))

/-- The model functor forgets the presentation, retaining the actual LetCase algebra. -/
noncomputable def forgetValidation (P : InstrSig τ ε) :
    (validatedRoom J P).Mod ⥤ ((LetCase.inst Γ₀).obj P).Mod :=
  ShrinkHoms.inverse.{0} (Discrete (ValidatedCaseAlgebra J P)) ⋙
    Discrete.functor ValidatedCaseAlgebra.algebra

/-- The model restriction keeps sentences and satisfaction unchanged. -/
noncomputable def restrictCaseCorridor (P : InstrSig τ ε) :
    (LetCase.inst Γ₀).obj P ⟶ validatedRoom J P :=
  ⟨id, forgetValidation J P, fun _ _ => Iff.rfl⟩

variable {J} (g : SignatureMap P.Instr Q.Instr τ υ ε δ) [g.PreservesProducts] [g.PreservesSums]

/-- Use the existing LetCase sentence map and the validated algebra reduct. -/
noncomputable def validatedCorridor : validatedRoom J P ⟶ validatedRoom J Q where
  sen := (PresSig.inst.map (typeCaseHom g)).sen
  mod := ShrinkHoms.inverse.{0} (Discrete (ValidatedCaseAlgebra J Q)) ⋙
    Discrete.functor (Discrete.mk ∘ ValidatedCaseAlgebra.reduct g) ⋙
    ShrinkHoms.functor.{0} (Discrete (ValidatedCaseAlgebra J P))
  sat A e := (PresSig.inst.map (typeCaseHom g)).sat A.fromShrinkHoms.as.algebra e

variable (J) [FreydCategory.CentralUnit J]

/-- Reify sentences and present each coherent SSA model as a validated LetCase algebra. -/
noncomputable def validatedReifyCorridor (P : InstrSig τ ε) :
    validatedRoom J P ⟶ ssaRoom J P where
  sen := reify
  mod := ShrinkHoms.inverse.{0} (Discrete (CoherentRegionModel J P)) ⋙
    Discrete.functor (Discrete.mk ∘ CoherentRegionModel.validate J) ⋙
    ShrinkHoms.functor.{0} (Discrete (ValidatedCaseAlgebra J P))
  sat K e := sat_reify_iff K.fromShrinkHoms.as e

/-- Compile sentences and expand each validated algebra using the recovered
primitive arrows. -/
noncomputable def validatedCompileCorridor (P : InstrSig τ ε) :
    ssaRoom J P ⟶ validatedRoom J P where
  sen := compile
  mod := ShrinkHoms.inverse.{0} (Discrete (ValidatedCaseAlgebra J P)) ⋙
    Discrete.functor (Discrete.mk ∘ ValidatedCaseAlgebra.expand) ⋙
    ShrinkHoms.functor.{0} (Discrete (CoherentRegionModel J P))
  sat A e :=
    (Iff.of_eq (congrArg (fun B => ((LetCase.inst Γ₀).obj P).Sat B (compile e))
      A.fromShrinkHoms.as.presentation.symm)).trans (sat_compile_iff A.fromShrinkHoms.as.expand e)

end Silmaril.Isotope.Institution.Acyclic
