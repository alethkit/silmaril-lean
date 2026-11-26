module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.IdentityLet.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.ITree.Thms

/-! # The weak ITree image of the guarded identity-let extension -/

public section

universe v q

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.IdentityLet

open CategoryTheory
open Paper.TypeCategory (ofType weakITreeFunctor)
open Semantics.Interaction Semantics.Interaction.Typed
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)

variable {κ : Type (v + 1)} [AtomValues κ] {E : Type v → Type v}
  {Φ : Type q} [HasTy Φ (Ty κ)] [HasEff Φ Bool]

attribute [local instance] typeModel categoricalInstructions

variable [InstructionModel Φ (Ty κ) Bool (ModelTree E)]
  (raw : Primitive E Φ (Sigma (AtomValues.carrier (κ := κ))))

/-- Any two guarded singleton arrows identified by the optional identity-let
equations have equal weak interaction trees in the compatible typed model. -/
theorem weakITree_image_eq_of_projection_eq
    (compat : Compatible (κ' := κ) ⟨fun f x =>
      InstructionModel.denote (τ := Ty κ) (ε := Bool) (m := ModelTree E) f x⟩ raw)
    {A B : Ty κ} (f g : ofType (Φ := Φ) A ⟶ ofType B)
    (eq : projection.map f = projection.map g) :
    (weakITreeFunctor raw compat).map f = (weakITreeFunctor raw compat).map g := by
  have := regionTypingCoherent raw compat
  exact denoteArrow_eq_of_projection_eq (typeJ (m := ModelTree E))
    (Semantics.Categorical.ofMonadicTypeModel (τ := Ty κ)) (fun _ _ => ⟨rfl, rfl⟩) f g eq

end Silmaril.Isotope.LambdaSSA.Region.Paper.IdentityLet
