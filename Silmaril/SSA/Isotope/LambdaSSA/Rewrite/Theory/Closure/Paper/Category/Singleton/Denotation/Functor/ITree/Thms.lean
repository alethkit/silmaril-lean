module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.ITree.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.Iteration.Thms

/-! # Representative evaluation and coproducts of the weak ITree functor -/

public section

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

/-- The functor computes the denotation of the given guarded representative. -/
theorem weakITreeFunctor_map_ofRegion
    (compat : Compatible (κ' := κ) ⟨fun f x =>
      InstructionModel.denote (τ := Ty κ) (ε := Bool) (m := ModelTree E) f x⟩ raw)
    {A B : Ty κ} {r : Region Φ} (hr : ValueBranches [A] r [B]) :
    (weakITreeFunctor raw compat).map (ofRegion hr) =
      Semantics.Categorical.denoteSingletonRegion (typeJ (m := ModelTree E))
        (Semantics.Categorical.ofMonadicTypeModel (τ := Ty κ)) hr.hasType := by
  have := regionTypingCoherent raw compat
  exact denoteArrow_ofRegion _ _ (fun _ _ => ⟨rfl, rfl⟩) hr

/-- In particular the weak ITree interpretation carries the chosen initial
object and binary coproducts to colimits. -/
theorem weakITreeFunctor_preservesFiniteCoproducts
    (compat : Compatible (κ' := κ) ⟨fun f x =>
      InstructionModel.denote (τ := Ty κ) (ε := Bool) (m := ModelTree E) f x⟩ raw) :
    PreservesFiniteCoproducts (weakITreeFunctor raw compat) := by
  have := regionTypingCoherent raw compat
  exact denoteFunctor_preservesFiniteCoproducts _ _ (fun _ _ => ⟨rfl, rfl⟩)

/-- The canonical categorical comparison is the inverse of the chosen sum isomorphism. -/
theorem weakITreeFunctor_coprodComparison
    (compat : Compatible (κ' := κ) ⟨fun f x =>
      InstructionModel.denote (τ := Ty κ) (ε := Bool) (m := ModelTree E) f x⟩ raw) (A B : Ty κ) :
    coprodComparison (weakITreeFunctor raw compat) (ofType A) (ofType B) =
      (weakITreeCoprodIso raw compat A B).inv := by
  have := regionTypingCoherent raw compat
  exact denoteFunctor_coprodComparison _ _ (fun _ _ => ⟨rfl, rfl⟩) A B

/-- The target iteration is the weak ITree Kleisli iterator and uses the
chosen coproduct comparison. -/
theorem weakITreeFunctor_map_iterate
    (compat : Compatible (κ' := κ) ⟨fun f x =>
      InstructionModel.denote (τ := Ty κ) (ε := Bool) (m := ModelTree E) f x⟩ raw)
    {A B : Ty κ} (f : ofType (Φ := Φ) A ⟶ ofType B ⨿ ofType A) :
    (weakITreeFunctor raw compat).map (Paper.TypeCategory.iterate f) =
      CategoryTheory.iterate ((weakITreeFunctor raw compat).map f ≫ (weakITreeCoprodIso raw compat B A).hom) := by
  have := regionTypingCoherent raw compat
  exact denoteFunctor_map_iterate _ _ (fun _ _ => ⟨rfl, rfl⟩) f

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
