module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Freyd.Native.Map.Defs
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Naturality.Thms

public section

universe u v w u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.Freyd.Native.Proofs

open CategoryTheory CategoryTheory.Limits
open Semantics.Categorical (TypeModel InstructionModel pair_pre_map)

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
    homMap J M h (ofExpr a) = J.map (singletonInput M X) ≫ f := by
  obtain ⟨d, hd⟩ := exists_lowering hf
  exact congrArg (fun v => J.map (singletonInput M X) ≫ v) ((h a a (.refl a.prop) _ d).trans hd)

theorem map_instruction {f : Φ} (hf : instrEff f ≤ e) (a : Hom Φ X (instrSrc f) e) :
    homMap J M h (Hom.applyInstruction hf a) = Freyd.applyInstruction J M f (homMap J M h a) := by
  induction a using Quotient.inductionOn with
  | _ a =>
    obtain ⟨_, ha⟩ := exists_denotes (J := J) (M := M) a.prop
    change homMap J M h (ofExpr ⟨.op f a.val, .op hf a.prop⟩) =
      Freyd.applyInstruction J M f (homMap J M h (ofExpr a))
    rw [homMap_of_denotes h _ (.op hf ha), homMap_of_denotes h a ha]
    unfold Freyd.applyInstruction
    exact (Category.assoc _ _ _).symm

theorem map_unit (X : τ) :
    homMap J M h (Hom.toUnit (X := X)) = Freyd.toUnit J M := by
  change homMap J M h (ofExpr ⟨.unit, Wf.unit [(X, ⊥)] e⟩) = _
  rw [homMap_of_denotes h _ (.unit [(X, ⊥)])]
  unfold Freyd.toUnit
  erw [← J.map_comp, CartesianMonoidalCategory.comp_toUnit_assoc]

theorem map_pair (a : Hom Φ X A e) (b : Hom Φ X B e) :
    homMap J M h (Hom.pair a b) = Freyd.pair J M (homMap J M h a) (homMap J M h b) := by
  induction a using Quotient.inductionOn with
  | _ a =>
    induction b using Quotient.inductionOn with
    | _ b =>
      obtain ⟨fa, ha⟩ := exists_denotes (J := J) (M := M) a.prop
      obtain ⟨fb, hb⟩ := exists_denotes (J := J) (M := M) b.prop
      change homMap J M h (ofExpr ⟨.pair a.val b.val, .pair a.prop b.prop⟩) =
        Freyd.pair J M (homMap J M h (ofExpr a)) (homMap J M h (ofExpr b))
      rw [homMap_of_denotes h _ (.pair ha hb), homMap_of_denotes h a ha,
        homMap_of_denotes h b hb]
      unfold Freyd.pair
      erw [← Category.assoc]
      exact congrArg (fun v => v ≫ J.map (M.productIso A B).inv)
        (pair_pre_map J (singletonInput M X) fa fb).symm

theorem map_inl (a : Hom Φ X A e) :
    homMap J M h (Hom.inl (B := B) a) = Freyd.inl J M (homMap J M h a) := by
  induction a using Quotient.inductionOn with
  | _ a =>
    obtain ⟨_, ha⟩ := exists_denotes (J := J) (M := M) a.prop
    change homMap J M h (ofExpr ⟨.inl a.val, Wf.inl (B := B) a.prop⟩) =
      Freyd.inl J M (homMap J M h (ofExpr a))
    rw [homMap_of_denotes h _ (.inl ha), homMap_of_denotes h a ha]
    unfold Freyd.inl
    exact (Category.assoc _ _ _).symm

theorem map_inr (b : Hom Φ X B e) :
    homMap J M h (Hom.inr (A := A) b) = Freyd.inr J M (homMap J M h b) := by
  induction b using Quotient.inductionOn with
  | _ b =>
    obtain ⟨_, hb⟩ := exists_denotes (J := J) (M := M) b.prop
    change homMap J M h (ofExpr ⟨.inr b.val, Wf.inr (A := A) b.prop⟩) =
      Freyd.inr J M (homMap J M h (ofExpr b))
    rw [homMap_of_denotes h _ (.inr hb), homMap_of_denotes h b hb]
    unfold Freyd.inr
    exact (Category.assoc _ _ _).symm

theorem map_abort (a : Hom Φ X empty e) :
    homMap J M h (Hom.abort (A := A) a) = Freyd.abort J M (homMap J M h a) := by
  induction a using Quotient.inductionOn with
  | _ a =>
    obtain ⟨_, ha⟩ := exists_denotes (J := J) (M := M) a.prop
    change homMap J M h (ofExpr ⟨.abort a.val, Wf.abort (A := A) a.prop⟩) =
      Freyd.abort J M (homMap J M h (ofExpr a))
    rw [homMap_of_denotes h _ (.abort ha), homMap_of_denotes h a ha]
    unfold Freyd.abort
    exact (Category.assoc _ _ _).symm

end Silmaril.Isotope.LetIter.PaperExpression.Source.Freyd.Native.Proofs
