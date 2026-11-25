module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Freyd.Native.Map.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.Freyd.Native.Map
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.Freyd.Native.Map.Reindex

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

/-- Evaluate the packed projection expression on a value-category input. -/
theorem denotes_project {Γ Δ : EffectCtx τ ε} {a : Expr Φ}
    {p : M.obj (packType Δ) ⟶ M.obj (packType Γ)}
    (i : Fin Γ.length) (ha : Denotes J M e Δ (packType Γ) a (J.map p)) :
    Denotes J M e Δ (Γ.get i).1 (project i.val a) (J.map (p ≫ Freyd.projection M Γ i)) :=
  Proofs.denotes_project M J i ha

/-- Substitution of the pure retained input reindexes a unary continuation,
whose body may be effectful at the original bound. -/
theorem denotes_subst_retained {D : τ} {b : Expr Φ} {f : Arrow J M (product unit (product X A)) D}
    (hb : Denotes J M e [(product X A, ⊥)] D b f) :
    Denotes J M e [(A, ⊥), (X, ⊥)] D
      (b.subst (Hom.extendedInput (Φ := Φ) (ε := ε) X A).val.subst0)
      (J.map (extendInputMap M (singletonProjection M X) A ≫ singletonInput M (product X A)) ≫ f) :=
  Proofs.denotes_subst_retained M J hb

/-- Substitution of the pure retained input with both product components
reindexes a binary continuation at the original effect bound. -/
theorem denotes_subst_retainedPair {D : τ} {b : Expr Φ}
    {f : Arrow J M (product unit (product (product X A) B)) D}
    (hb : Denotes J M e [(product (product X A) B, ⊥)] D b f) :
    Denotes J M e [(B, ⊥), (A, ⊥), (X, ⊥)] D
      (b.subst (Hom.extendedPairInput (Φ := Φ) (ε := ε) X A B).val.subst0)
      (J.map (extendInputMap M (extendInputMap M (singletonProjection M X) A) B ≫
        singletonInput M (product (product X A) B)) ≫ f) :=
  Proofs.denotes_subst_retainedPair M J hb

theorem map_projection (Γ : EffectCtx τ ε) (i : Fin Γ.length) :
    homMap J M h (Hom.projection Γ i) = J.map (Freyd.projection M Γ i) :=
  Proofs.map_projection h Γ i

theorem map_bind {D : τ} (a : Hom Φ X A e) (b : Hom Φ (product X A) D e) :
    homMap J M h (Hom.bind a b) = Freyd.bind J M (homMap J M h a) (homMap J M h b) :=
  Proofs.map_bind h a b

theorem map_bindPair {D : τ} (a : Hom Φ X (product A B) e)
    (b : Hom Φ (product (product X A) B) D e) :
    homMap J M h (Hom.bindPair a b) = Freyd.bindPair J M (homMap J M h a) (homMap J M h b) :=
  Proofs.map_bindPair h a b

theorem map_case {D : τ} (a : Hom Φ X (coprod A B) e)
    (l : Hom Φ (product X A) D e) (r : Hom Φ (product X B) D e) :
    homMap J M h (Hom.caseWithContext a l r) =
      Freyd.caseWithContext J M (homMap J M h a) (homMap J M h l) (homMap J M h r) :=
  Proofs.map_case h a l r

/-- Native loop-free denotation supplies all operations of the fixed-effect
Freyd comparison once source-equation soundness is supplied. -/
@[expose] noncomputable def comparison : Comparison J M Φ e where
  map := homMap J M h
  map_projection := map_projection h
  map_instruction := map_instruction h
  map_unit := map_unit h
  map_pair := map_pair h
  map_bind := map_bind h
  map_bindPair := map_bindPair h
  map_inl := map_inl h
  map_inr := map_inr h
  map_case := map_case h
  map_abort := map_abort h

end Silmaril.Isotope.LetIter.PaperExpression.Source.Freyd.Native
