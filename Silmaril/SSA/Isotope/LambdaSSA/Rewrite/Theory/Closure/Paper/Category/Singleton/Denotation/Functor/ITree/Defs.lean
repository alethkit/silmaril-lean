module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.Coproducts.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Thms

/-! # The weak ITree interpretation of the guarded Paper singleton category -/

@[expose] public section

universe v q

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Semantics.Interaction Semantics.Interaction.Typed

variable {κ : Type (v + 1)} [AtomValues κ] {E : Type v → Type v}
  {Φ : Type q} [HasTy Φ (Ty κ)] [HasEff Φ Bool]

attribute [local instance] typeModel categoricalInstructions

variable [InstructionModel Φ (Ty κ) Bool (ModelTree E)]
  (raw : Primitive E Φ (Sigma (AtomValues.carrier (κ := κ))))

/-- Interpret every guarded Paper singleton arrow in the weak ITree Kleisli
category, using the same primitives and reply continuations as the erased evaluator. -/
noncomputable def weakITreeFunctor
    (compat : Compatible (κ' := κ) ⟨fun f x =>
      InstructionModel.denote (τ := Ty κ) (ε := Bool) (m := ModelTree E) f x⟩ raw) :
    TypeCategory (τ := Ty κ) Φ ⥤ Kleisli (ofTypeMonad (ModelTree E)) :=
  letI := regionTypingCoherent raw compat
  denoteFunctor (typeJ (m := ModelTree E)) (Semantics.Categorical.ofMonadicTypeModel (τ := Ty κ))
    (fun _ _ => ⟨rfl, rfl⟩)

/-- The chosen coproduct comparison in the weak ITree model. -/
noncomputable def weakITreeCoprodIso
    (compat : Compatible (κ' := κ) ⟨fun f x =>
      InstructionModel.denote (τ := Ty κ) (ε := Bool) (m := ModelTree E) f x⟩ raw) (A B : Ty κ) :
    (weakITreeFunctor raw compat).obj (ofType A ⨿ ofType B) ≅
      (weakITreeFunctor raw compat).obj (ofType A) ⨿ (weakITreeFunctor raw compat).obj (ofType B) :=
  letI := regionTypingCoherent raw compat
  denoteCoprodIso (typeJ (m := ModelTree E)) (Semantics.Categorical.ofMonadicTypeModel (τ := Ty κ))
    (fun _ _ => ⟨rfl, rfl⟩) A B

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
