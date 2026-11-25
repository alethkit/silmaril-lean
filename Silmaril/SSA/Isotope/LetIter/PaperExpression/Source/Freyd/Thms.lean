module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Freyd.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.Freyd

/-! # Comparison with the packed Freyd interpretation at the original bound -/

public section

universe u v w u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.Freyd

open CategoryTheory CategoryTheory.Limits
open Semantics.Categorical (TypeModel InstructionModel)

variable {τ : Type u} {Φ : Type v} {ε : Type w} [TypeFormers τ]
  [HasTy Φ τ] [HasEff Φ ε] [Preorder ε] [OrderBot ε]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  {J : V ⥤ C} {M : TypeModel τ V} [DistributiveFreydCategory J] [InstructionModel J M Φ]
  {Γ : EffectCtx τ ε} {A : τ} {a : Expr Φ} {e : ε}
  {f : Arrow J M (packType Γ) A}

theorem Denotes.wf (h : Denotes J M e Γ A a f) : Wf Γ a A e :=
  Proofs.wf h

/-- A typed source expression admits an interpretation in the supplied
distributive Freyd structure. -/
theorem exists_denotes (h : Wf Γ a A e) : ∃ f, Denotes J M e Γ A a f :=
  Proofs.exists_denotes h

/-- An operation-preserving map sends the packed source interpreter to the
chosen Freyd interpretation at the common effect bound. -/
theorem Comparison.map_denote (F : Comparison J M Φ e) (h : Denotes J M e Γ A a f) :
    F.map (Source.denote ⟨a, h.wf⟩) = f :=
  Proofs.map_denote F h

/-- The Freyd interpretation is precisely the image of the packed source
denotation under a supplied comparison. -/
theorem Comparison.denotes_iff (F : Comparison J M Φ e) (a : TypedExpr Φ Γ A e) :
    Denotes J M e Γ A a.val f ↔ F.map (Source.denote a) = f :=
  Proofs.denotes_iff F a

/-- The same comparison written using the fixed-effect packing map. -/
theorem Comparison.denotes_iff_map_pack (F : Comparison J M Φ e) (a : TypedExpr Φ Γ A e) :
    Denotes J M e Γ A a.val f ↔ F.map (pack (ofExpr a)) = f := by
  rw [← denote_eq_pack, F.denotes_iff]

end Silmaril.Isotope.LetIter.PaperExpression.Source.Freyd
