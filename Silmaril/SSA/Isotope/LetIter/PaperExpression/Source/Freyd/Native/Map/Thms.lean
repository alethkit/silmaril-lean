module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Freyd.Native.Map.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.Freyd.Native.Map

/-! # Operation laws of the native representative map -/

public section

universe u v w u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.Freyd.Native

open CategoryTheory CategoryTheory.Limits
open Semantics.Categorical (TypeModel InstructionModel)

variable {τ : Type u} {Φ : Type v} {ε : Type w} [TypeFormers τ]
  {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  {C : Type u₂} [Category.{v₂} C] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  {J : V ⥤ C} {M : TypeModel τ V} [DistributiveFreydCategory J] [HasTy Φ τ] [InstructionModel J M Φ]
  [HasEff Φ ε] [Preorder ε] [OrderBot ε]
  {X A B : τ} {e : ε} (h : RespectsSourceEqv (Φ := Φ) J M e)

theorem homMap_of_denotes (a : TypedExpr Φ [(X, ⊥)] A e)
    {f : Arrow J M (product unit X) A} (hf : Denotes J M e [(X, ⊥)] A a.val f) :
    homMap J M h (ofExpr a) = J.map (singletonInput M X) ≫ f :=
  Proofs.homMap_of_denotes h a hf

theorem map_instruction {f : Φ} (hf : instrEff f ≤ e) (a : Hom Φ X (instrSrc f) e) :
    homMap J M h (Hom.applyInstruction hf a) = Freyd.applyInstruction J M f (homMap J M h a) :=
  Proofs.map_instruction h hf a

theorem map_unit (X : τ) :
    homMap J M h (Hom.toUnit (X := X)) = Freyd.toUnit J M :=
  Proofs.map_unit h X

theorem map_pair (a : Hom Φ X A e) (b : Hom Φ X B e) :
    homMap J M h (Hom.pair a b) = Freyd.pair J M (homMap J M h a) (homMap J M h b) :=
  Proofs.map_pair h a b

theorem map_inl (a : Hom Φ X A e) :
    homMap J M h (Hom.inl (B := B) a) = Freyd.inl J M (homMap J M h a) :=
  Proofs.map_inl h a

theorem map_inr (b : Hom Φ X B e) :
    homMap J M h (Hom.inr (A := A) b) = Freyd.inr J M (homMap J M h b) :=
  Proofs.map_inr h b

theorem map_abort (a : Hom Φ X empty e) :
    homMap J M h (Hom.abort (A := A) a) = Freyd.abort J M (homMap J M h a) :=
  Proofs.map_abort h a

end Silmaril.Isotope.LetIter.PaperExpression.Source.Freyd.Native
