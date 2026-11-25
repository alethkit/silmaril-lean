module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Freyd.Native.Map.Defs
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Naturality.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.Freyd.Native.Map.Reindex

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

theorem map_projection (Γ : EffectCtx τ ε) (i : Fin Γ.length) :
    homMap J M h (Hom.projection Γ i) = J.map (Freyd.projection M Γ i) := by
  let X := packType Γ
  let a : TypedExpr Φ [(X, ⊥)] (Γ.get i).1 e :=
    ⟨project i.val (.var 0), Hom.projection_wf Γ i⟩
  have hv : Denotes J M e [(X, ⊥)] X (.var 0 : Expr Φ) (J.map (singletonProjection M X)) :=
    .var (Γ := [(X, ⊥)]) 0 bot_le
  change homMap J M h (ofExpr a) = _
  rw [homMap_of_denotes h a (denotes_project M J i hv)]
  erw [← J.map_comp, ← Category.assoc, singletonInput_projection M, Category.id_comp]

omit [SymmetricCategory V] [DistributiveTensor V] in
private theorem retained_cancel (X A : τ) :
    extendInputMap M (singletonInput M X) A ≫ extendInputMap M (singletonProjection M X) A =
      𝟙 (M.obj (product X A)) := by
  rw [extendInputMap_comp M, singletonInput_projection M, extendInputMap_id M]

omit [SymmetricCategory V] [DistributiveTensor V] in
private theorem retainedPair_cancel (X A B : τ) :
    extendInputMap M (extendInputMap M (singletonInput M X) A) B ≫
      extendInputMap M (extendInputMap M (singletonProjection M X) A) B =
        𝟙 (M.obj (product (product X A) B)) := by
  rw [extendInputMap_comp M, retained_cancel (M := M), extendInputMap_id M]

omit [CartesianMonoidalCategory V] [HasFiniteCoproducts V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C] [DistributiveFreydCategory J] in
private theorem map_cancel {R S T : V} {D : C} {p : R ⟶ S} {q : S ⟶ R} (hp : p ≫ q = 𝟙 R)
    (u : R ⟶ T) (f : J.obj T ⟶ D) :
    J.map p ≫ J.map (q ≫ u) ≫ f = J.map u ≫ f := by
  rw [← J.map_comp_assoc, ← Category.assoc, hp, Category.id_comp]

theorem map_bind {D : τ} (a : Hom Φ X A e) (b : Hom Φ (product X A) D e) :
    homMap J M h (Hom.bind a b) = Freyd.bind J M (homMap J M h a) (homMap J M h b) := by
  induction a using Quotient.inductionOn with
  | _ a =>
    induction b using Quotient.inductionOn with
    | _ b =>
      obtain ⟨_, ha⟩ := exists_denotes (J := J) (M := M) a.prop
      obtain ⟨_, hb⟩ := exists_denotes (J := J) (M := M) b.prop
      let input := Hom.extendedInput (Φ := Φ) (ε := ε) X A
      let t : TypedExpr Φ [(X, ⊥)] D e :=
        ⟨.let₁ a.val (b.val.subst input.val.subst0), .let₁ a.prop (Hom.substInput_wf input b)⟩
      change homMap J M h (ofExpr t) = Freyd.bind J M (homMap J M h (ofExpr a)) (homMap J M h (ofExpr b))
      rw [homMap_of_denotes h t (.let1 ha (denotes_subst_retained M J hb)),
        homMap_of_denotes h a ha, homMap_of_denotes h b hb]
      erw [← bind_reindex M J (singletonInput M X)]
      erw [map_cancel (J := J) (retained_cancel (M := M) X A)]

theorem map_bindPair {D : τ} (a : Hom Φ X (product A B) e)
    (b : Hom Φ (product (product X A) B) D e) :
    homMap J M h (Hom.bindPair a b) = Freyd.bindPair J M (homMap J M h a) (homMap J M h b) := by
  induction a using Quotient.inductionOn with
  | _ a =>
    induction b using Quotient.inductionOn with
    | _ b =>
      obtain ⟨_, ha⟩ := exists_denotes (J := J) (M := M) a.prop
      obtain ⟨_, hb⟩ := exists_denotes (J := J) (M := M) b.prop
      let input := Hom.extendedPairInput (Φ := Φ) (ε := ε) X A B
      let t : TypedExpr Φ [(X, ⊥)] D e :=
        ⟨.let₂ a.val (b.val.subst input.val.subst0), .let₂ a.prop (Hom.substInput_wf input b)⟩
      change homMap J M h (ofExpr t) = Freyd.bindPair J M (homMap J M h (ofExpr a)) (homMap J M h (ofExpr b))
      rw [homMap_of_denotes h t (.let2 ha (denotes_subst_retainedPair M J hb)),
        homMap_of_denotes h a ha, homMap_of_denotes h b hb]
      erw [← bindPair_reindex M J (singletonInput M X)]
      erw [map_cancel (J := J) (retainedPair_cancel (M := M) X A B)]

theorem map_case {D : τ} (a : Hom Φ X (coprod A B) e)
    (l : Hom Φ (product X A) D e) (r : Hom Φ (product X B) D e) :
    homMap J M h (Hom.caseWithContext a l r) =
      Freyd.caseWithContext J M (homMap J M h a) (homMap J M h l) (homMap J M h r) := by
  induction a using Quotient.inductionOn with
  | _ a =>
    induction l using Quotient.inductionOn with
    | _ l =>
      induction r using Quotient.inductionOn with
      | _ r =>
        obtain ⟨_, ha⟩ := exists_denotes (J := J) (M := M) a.prop
        obtain ⟨_, hl⟩ := exists_denotes (J := J) (M := M) l.prop
        obtain ⟨_, hr⟩ := exists_denotes (J := J) (M := M) r.prop
        let left := Hom.extendedInput (Φ := Φ) (ε := ε) X A
        let right := Hom.extendedInput (Φ := Φ) (ε := ε) X B
        let t : TypedExpr Φ [(X, ⊥)] D e :=
          ⟨.case a.val (l.val.subst left.val.subst0) (r.val.subst right.val.subst0),
            .case a.prop (Hom.substInput_wf left l) (Hom.substInput_wf right r)⟩
        change homMap J M h (ofExpr t) =
          Freyd.caseWithContext J M
            (homMap J M h (ofExpr a)) (homMap J M h (ofExpr l)) (homMap J M h (ofExpr r))
        rw [homMap_of_denotes h t (.case ha (denotes_subst_retained M J hl) (denotes_subst_retained M J hr)),
          homMap_of_denotes h a ha, homMap_of_denotes h l hl, homMap_of_denotes h r hr]
        erw [← case_reindex M J (singletonInput M X)]
        erw [map_cancel (J := J) (retained_cancel (M := M) X A),
          map_cancel (J := J) (retained_cancel (M := M) X B)]

end Silmaril.Isotope.LetIter.PaperExpression.Source.Freyd.Native.Proofs
