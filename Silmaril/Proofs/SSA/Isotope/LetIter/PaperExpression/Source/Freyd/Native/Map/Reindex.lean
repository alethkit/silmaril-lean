module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Freyd.Native.Map.Defs
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Naturality.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms

public section

universe u v w u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.Freyd.Native.Proofs

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped MonoidalCategory
open Semantics.Categorical (TypeModel InstructionModel bind_pre_map pair_pre_map case_pre_map extend_map)

variable {τ : Type u} {Φ : Type v} {ε : Type w} [TypeFormers τ]
  {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (M : TypeModel τ V)

private def packedFst (X A : τ) : M.obj (product X A) ⟶ M.obj X :=
  (M.productIso X A).hom ≫ fst _ _

private def packedSnd (X A : τ) : M.obj (product X A) ⟶ M.obj A :=
  (M.productIso X A).hom ≫ snd _ _

private theorem projection_zero (Γ : EffectCtx τ ε) (A : τ) (d : ε) :
    Freyd.projection M ((A, d) :: Γ) 0 = packedSnd M (packType Γ) A :=
  rfl

private theorem projection_succ (Γ : EffectCtx τ ε) (A : τ) (d : ε)
    (i : Fin Γ.length) :
    Freyd.projection M ((A, d) :: Γ) i.succ = packedFst M (packType Γ) A ≫ Freyd.projection M Γ i :=
  (Category.assoc _ _ _).symm

theorem singletonInput_projection (X : τ) :
    singletonInput M X ≫ singletonProjection M X = 𝟙 _ := by
  simp [singletonInput, singletonProjection]

private theorem extendInputMap_fst {X Y : τ} (k : M.obj X ⟶ M.obj Y) (A : τ) :
    extendInputMap M k A ≫ packedFst M Y A = packedFst M X A ≫ k := by
  simp [extendInputMap, packedFst]

private theorem extendInputMap_snd {X Y : τ} (k : M.obj X ⟶ M.obj Y) (A : τ) :
    extendInputMap M k A ≫ packedSnd M Y A = packedSnd M X A := by
  simp [extendInputMap, packedSnd]

private theorem extendInputMap_eq_lift {X Y : τ} (k : M.obj X ⟶ M.obj Y) (A : τ) :
    extendInputMap M k A =
      lift (packedFst M X A ≫ k) (packedSnd M X A) ≫ (M.productIso Y A).inv := by
  rw [← cancel_mono (M.productIso Y A).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply CartesianMonoidalCategory.hom_ext
  · simp [extendInputMap, packedFst]
  · simp [extendInputMap, packedSnd]

theorem extendInputMap_comp {X Y Z : τ} (p : M.obj X ⟶ M.obj Y) (q : M.obj Y ⟶ M.obj Z) (A : τ) :
    extendInputMap M p A ≫ extendInputMap M q A = extendInputMap M (p ≫ q) A := by
  simp [extendInputMap, Category.assoc]

theorem extendInputMap_id (X A : τ) :
    extendInputMap M (𝟙 (M.obj X)) A = 𝟙 _ := by
  simp [extendInputMap]

private theorem bind_input_square {X Y : τ} (k : M.obj X ⟶ M.obj Y) (A : τ) :
    (M.productIso X A).inv ≫ extendInputMap M k A = (k ▷ M.obj A) ≫ (M.productIso Y A).inv := by
  simp [extendInputMap]

private theorem pair_input_square {X Y : τ} (k : M.obj X ⟶ M.obj Y) (A B : τ) :
    Freyd.pairExtension M X A B ≫ extendInputMap M (extendInputMap M k A) B =
      (k ▷ M.obj (product A B)) ≫ Freyd.pairExtension M Y A B := by
  simp only [Freyd.pairExtension, extendInputMap, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← MonoidalCategory.comp_whiskerRight_assoc, Iso.inv_hom_id_assoc,
    MonoidalCategory.comp_whiskerRight_assoc,
    ← MonoidalCategory.associator_inv_naturality_left_assoc,
    MonoidalCategory.whisker_exchange_assoc]

private theorem pairExtension_fst (X A B : τ) :
    Freyd.pairExtension M X A B ≫ packedFst M (product X A) B ≫ packedSnd M X A =
      snd (M.obj X) (M.obj (product A B)) ≫ packedFst M A B := by
  simp [Freyd.pairExtension, packedFst, packedSnd]

private theorem pairExtension_snd (X A B : τ) :
    Freyd.pairExtension M X A B ≫ packedSnd M (product X A) B =
      snd (M.obj X) (M.obj (product A B)) ≫ packedSnd M A B := by
  simp [Freyd.pairExtension, packedSnd]

variable {C : Type u₂} [Category.{v₂} C] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) [DistributiveFreydCategory J]

omit [CartesianMonoidalCategory V] [HasFiniteCoproducts V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C] [DistributiveFreydCategory J] in
private theorem map_assoc_of_square {R S T U : V} {B : C}
    {p : R ⟶ S} {q : S ⟶ U} {r : R ⟶ T} {s : T ⟶ U}
    (h : p ≫ q = r ≫ s) (g : J.obj U ⟶ B) :
    J.map p ≫ J.map q ≫ g = J.map r ≫ J.map s ≫ g := by
  rw [← J.map_comp_assoc, ← J.map_comp_assoc, h]

theorem bind_reindex {X Y A B : τ} (k : M.obj X ⟶ M.obj Y)
    (f : Arrow J M Y A) (g : Arrow J M (product Y A) B) :
    Freyd.bind J M (X := X) (A := A) (B := B)
      (J.map k ≫ f) (J.map (extendInputMap M k A) ≫ g) =
        J.map k ≫ Freyd.bind J M f g := by
  unfold Freyd.bind
  rw [map_assoc_of_square J (bind_input_square M k A) g, bind_pre_map]

theorem bindPair_reindex {X Y A B D : τ} (k : M.obj X ⟶ M.obj Y)
    (f : Arrow J M Y (product A B)) (g : Arrow J M (product (product Y A) B) D) :
    Freyd.bindPair J M (X := X) (A := A) (B := B) (D := D)
      (J.map k ≫ f) (J.map (extendInputMap M (extendInputMap M k A) B) ≫ g) =
        J.map k ≫ Freyd.bindPair J M f g := by
  unfold Freyd.bindPair
  rw [map_assoc_of_square J (pair_input_square M k A B) g, bind_pre_map]

theorem case_reindex {X Y A B D : τ} (k : M.obj X ⟶ M.obj Y)
    (f : Arrow J M Y (coprod A B)) (l : Arrow J M (product Y A) D)
    (r : Arrow J M (product Y B) D) :
    Freyd.caseWithContext J M (X := X) (A := A) (B := B) (D := D)
      (J.map k ≫ f) (J.map (extendInputMap M k A) ≫ l) (J.map (extendInputMap M k B) ≫ r) =
        J.map k ≫ Freyd.caseWithContext J M f l r := by
  unfold Freyd.caseWithContext
  rw [map_assoc_of_square J (bind_input_square M k A) l,
    map_assoc_of_square J (bind_input_square M k B) r, Category.assoc, case_pre_map]

private theorem pair_reindex {X Y A B : τ} (k : M.obj X ⟶ M.obj Y)
    (f : Arrow J M Y A) (g : Arrow J M Y B) :
    Freyd.pair J M (X := X) (A := A) (B := B) (J.map k ≫ f) (J.map k ≫ g) =
      J.map k ≫ Freyd.pair J M f g := by
  unfold Freyd.pair
  rw [pair_pre_map, Category.assoc]

private theorem pure_pair {X A B : τ} (p : M.obj X ⟶ M.obj A) (q : M.obj X ⟶ M.obj B) :
    Freyd.pair J M (X := X) (A := A) (B := B) (J.map p) (J.map q) =
      J.map (lift p q ≫ (M.productIso A B).inv) := by
  unfold Freyd.pair ProofRelevant.Semantics.Categorical.pair
    ProofRelevant.Semantics.Categorical.bind ProofRelevant.Semantics.Categorical.retainedContext
  simp only [← J.map_comp, extend_map]
  congr 1
  simp [comp_lift]

private theorem pure_bindPair {X A B D : τ} (p : M.obj X ⟶ M.obj (product A B))
    (q : M.obj (product (product X A) B) ⟶ M.obj D) :
    Freyd.bindPair J M (X := X) (A := A) (B := B) (D := D) (J.map p) (J.map q) =
      J.map (lift (𝟙 _) p ≫ Freyd.pairExtension M X A B ≫ q) := by
  simp only [Freyd.bindPair, ProofRelevant.Semantics.Categorical.bind, extend_map,
    ← J.map_comp]

variable [HasTy Φ τ] [HasEff Φ ε] [Preorder ε] [OrderBot ε] [InstructionModel J M Φ]

-- The retained input uses only lookups and pairing. The type bound alone
-- does not assert that an arbitrary instruction has a value denotation.
private inductive TupleDenotes (e : ε) (Γ : EffectCtx τ ε) :
    (A : τ) → Expr Φ → (M.obj (packType Γ) ⟶ M.obj A) → Prop where
  | var (i : Fin Γ.length) : (Γ.get i).2 ≤ e →
      TupleDenotes e Γ (Γ.get i).1 (.var i.val) (Freyd.projection M Γ i)
  | pair {A B a b p q} :
      TupleDenotes e Γ A a p → TupleDenotes e Γ B b q →
      TupleDenotes e Γ (product A B) (.pair a b) (lift p q ≫ (M.productIso A B).inv)

private theorem tuple_denotes {e : ε} {Γ : EffectCtx τ ε} {A : τ}
    {a : Expr Φ} {p : M.obj (packType Γ) ⟶ M.obj A} (h : TupleDenotes M e Γ A a p) :
    Denotes J M e Γ A a (J.map p) := by
  induction h with
  | var i hi => exact .var i hi
  | pair _ _ ha hb =>
    rw [← pure_pair M J]
    exact .pair ha hb

omit [SymmetricCategory V] [DistributiveTensor V] [HasTy Φ τ] [HasEff Φ ε] in
private theorem tuple_wk0 {e : ε} {Γ : EffectCtx τ ε} {A : τ}
    {a : Expr Φ} {p : M.obj (packType Γ) ⟶ M.obj A}
    (h : TupleDenotes M e Γ A a p) (B : τ) :
    TupleDenotes M e ((B, ⊥) :: Γ) A a.wk0 (packedFst M (packType Γ) B ≫ p) := by
  induction h with
  | var i hi =>
    erw [← projection_succ M Γ B ⊥ i]
    exact .var (Γ := ((B, ⊥) :: Γ)) i.succ hi
  | pair _ _ ha hb =>
    erw [← Category.assoc, comp_lift]
    exact .pair ha hb

private def Slots (e : ε) (Γ Δ : EffectCtx τ ε) (σ : Nat → Expr Φ)
    (k : M.obj (packType Δ) ⟶ M.obj (packType Γ)) : Prop :=
  ∀ i : Fin Γ.length, (Γ.get i).2 ≤ e →
    TupleDenotes M e Δ (Γ.get i).1 (σ i.val) (k ≫ Freyd.projection M Γ i)

omit [SymmetricCategory V] [DistributiveTensor V] [HasTy Φ τ] [HasEff Φ ε] in
private theorem slots_lift {e : ε} {Γ Δ : EffectCtx τ ε} {σ : Nat → Expr Φ}
    {k : M.obj (packType Δ) ⟶ M.obj (packType Γ)} (h : Slots M e Γ Δ σ k) (A : τ) :
    Slots M e ((A, ⊥) :: Γ) ((A, ⊥) :: Δ) (Expr.liftSubst σ) (extendInputMap M k A) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · intro hi
    erw [projection_zero M Γ A ⊥, extendInputMap_snd]
    exact .var 0 hi
  · intro hi
    erw [projection_succ M Γ A ⊥ j, ← Category.assoc, extendInputMap_fst, Category.assoc]
    exact tuple_wk0 M (h j hi) A

private theorem subst_denotes {e : ε} {Γ Δ : EffectCtx τ ε} {A : τ} {a : Expr Φ}
    {f : Arrow J M (packType Γ) A} (ha : Denotes J M e Γ A a f)
    {σ : Nat → Expr Φ} {k : M.obj (packType Δ) ⟶ M.obj (packType Γ)} (hs : Slots M e Γ Δ σ k) :
    Denotes J M e Δ A (a.subst σ) (J.map k ≫ f) := by
  induction ha generalizing Δ σ with
  | var i hi =>
    rw [← J.map_comp]
    exact tuple_denotes M J (hs i hi)
  | op hf _ ih =>
    unfold Freyd.applyInstruction
    rw [← Category.assoc]
    exact .op hf (ih hs)
  | let1 _ _ ih₁ ih₂ =>
    erw [← bind_reindex M J k]
    exact .let1 (ih₁ hs) (ih₂ (slots_lift M hs _))
  | pair _ _ ih₁ ih₂ =>
    rw [← pair_reindex M J k]
    exact .pair (ih₁ hs) (ih₂ hs)
  | unit =>
    unfold Freyd.toUnit
    rw [← J.map_comp, comp_toUnit_assoc]
    exact .unit Δ
  | let2 _ _ ih₁ ih₂ =>
    erw [← bindPair_reindex M J k]
    exact .let2 (ih₁ hs) (ih₂ (slots_lift M (slots_lift M hs _) _))
  | inl _ ih =>
    unfold Freyd.inl
    rw [← Category.assoc]
    exact .inl (ih hs)
  | inr _ ih =>
    unfold Freyd.inr
    rw [← Category.assoc]
    exact .inr (ih hs)
  | case _ _ _ ih₁ ih₂ ih₃ =>
    erw [← case_reindex M J k]
    exact .case (ih₁ hs) (ih₂ (slots_lift M hs _)) (ih₃ (slots_lift M hs _))
  | abort _ ih =>
    unfold Freyd.abort
    rw [← Category.assoc]
    exact .abort (ih hs)

omit [SymmetricCategory V] [DistributiveTensor V] [HasTy Φ τ] [HasEff Φ ε] in
private theorem tuple_extend {e : ε} {Γ : EffectCtx τ ε} {X : τ}
    {a : Expr Φ} {p : M.obj (packType Γ) ⟶ M.obj X}
    (h : TupleDenotes M e Γ X a p) (A : τ) :
    TupleDenotes M e ((A, ⊥) :: Γ) (product X A) (.pair a.wk0 (.var 0))
      (extendInputMap M p A) := by
  erw [extendInputMap_eq_lift, ← projection_zero M Γ A (⊥ : ε)]
  exact .pair (tuple_wk0 M h A) (.var 0 bot_le)

private theorem subst_singleton {e : ε} {Δ : EffectCtx τ ε} {X D : τ} {b a : Expr Φ}
    {f : Arrow J M (product unit X) D} {p : M.obj (packType Δ) ⟶ M.obj X}
    (hb : Denotes J M e [(X, ⊥)] D b f) (ha : TupleDenotes M e Δ X a p) :
    Denotes J M e Δ D (b.subst a.subst0) (J.map (p ≫ singletonInput M X) ≫ f) := by
  apply subst_denotes M J hb
  intro i
  refine Fin.cases ?_ (fun j => j.elim0) i
  intro _
  erw [projection_zero M [] X (⊥ : ε), Category.assoc]
  change TupleDenotes M e Δ X a (p ≫ (singletonInput M X ≫ singletonProjection M X))
  rw [singletonInput_projection, Category.comp_id]
  exact ha

theorem denotes_subst_retained {e : ε} {X A D : τ} {b : Expr Φ}
    {f : Arrow J M (product unit (product X A)) D}
    (hb : Denotes J M e [(product X A, ⊥)] D b f) :
    Denotes J M e [(A, ⊥), (X, ⊥)] D
      (b.subst (Hom.extendedInput (Φ := Φ) (ε := ε) X A).val.subst0)
      (J.map (extendInputMap M (singletonProjection M X) A ≫ singletonInput M (product X A)) ≫ f) :=
  subst_singleton M J hb (tuple_extend M (.var (Γ := [(X, ⊥)]) 0 bot_le) A)

theorem denotes_subst_retainedPair {e : ε} {X A B D : τ} {b : Expr Φ}
    {f : Arrow J M (product unit (product (product X A) B)) D}
    (hb : Denotes J M e [(product (product X A) B, ⊥)] D b f) :
    Denotes J M e [(B, ⊥), (A, ⊥), (X, ⊥)] D
      (b.subst (Hom.extendedPairInput (Φ := Φ) (ε := ε) X A B).val.subst0)
      (J.map (extendInputMap M (extendInputMap M (singletonProjection M X) A) B ≫
        singletonInput M (product (product X A) B)) ≫ f) :=
  subst_singleton M J hb (tuple_extend M (tuple_extend M (.var (Γ := [(X, ⊥)]) 0 bot_le) A) B)

private theorem denotes_first {e : ε} {Δ : EffectCtx τ ε} {X A : τ} {a : Expr Φ}
    {p : M.obj (packType Δ) ⟶ M.obj (product X A)}
    (ha : Denotes J M e Δ (product X A) a (J.map p)) :
    Denotes J M e Δ X (first a) (J.map (p ≫ packedFst M X A)) := by
  let i : Fin ((A, (⊥ : ε)) :: (X, ⊥) :: Δ).length := (0 : Fin ((X, (⊥ : ε)) :: Δ).length).succ
  have h := Denotes.let2 ha (Denotes.var (Γ := (A, ⊥) :: (X, ⊥) :: Δ) i (bot_le (a := e)))
  have hp : lift (𝟙 _) p ≫ Freyd.pairExtension M (packType Δ) X A ≫
      Freyd.projection M ((A, ⊥) :: (X, ⊥) :: Δ) i = p ≫ packedFst M X A := by
    unfold i
    erw [projection_succ M ((X, ⊥) :: Δ) A ⊥, projection_zero M Δ X ⊥]
    change lift (𝟙 _) p ≫ Freyd.pairExtension M (packType Δ) X A ≫
      packedFst M (product (packType Δ) X) A ≫ packedSnd M (packType Δ) X = _
    rw [pairExtension_fst M, lift_snd_assoc]
  erw [pure_bindPair M J, hp] at h
  exact h

private theorem denotes_second {e : ε} {Δ : EffectCtx τ ε} {X A : τ} {a : Expr Φ}
    {p : M.obj (packType Δ) ⟶ M.obj (product X A)}
    (ha : Denotes J M e Δ (product X A) a (J.map p)) :
    Denotes J M e Δ A (second a) (J.map (p ≫ packedSnd M X A)) := by
  have h := Denotes.let2 ha (Denotes.var (Γ := (A, ⊥) :: (X, ⊥) :: Δ) 0 (bot_le (a := e)))
  have hp : lift (𝟙 _) p ≫ Freyd.pairExtension M (packType Δ) X A ≫
      Freyd.projection M ((A, (⊥ : ε)) :: (X, ⊥) :: Δ) 0 = p ≫ packedSnd M X A := by
    erw [projection_zero M ((X, ⊥) :: Δ) A ⊥]
    change lift (𝟙 _) p ≫ Freyd.pairExtension M (packType Δ) X A ≫
      packedSnd M (product (packType Δ) X) A = _
    rw [pairExtension_snd M, lift_snd_assoc]
  erw [pure_bindPair M J, hp] at h
  exact h

theorem denotes_project {e : ε} {Γ Δ : EffectCtx τ ε} {a : Expr Φ}
    {p : M.obj (packType Δ) ⟶ M.obj (packType Γ)}
    (i : Fin Γ.length) (ha : Denotes J M e Δ (packType Γ) a (J.map p)) :
    Denotes J M e Δ (Γ.get i).1 (project i.val a) (J.map (p ≫ Freyd.projection M Γ i)) := by
  induction Γ generalizing a with
  | nil => exact i.elim0
  | cons slot Γ ih =>
    obtain ⟨A, d⟩ := slot
    revert i
    refine Fin.cases ?_ (fun i => ?_)
    · erw [projection_zero M Γ A d]
      exact denotes_second M J ha
    · erw [projection_succ M Γ A d i, ← Category.assoc]
      exact ih i (denotes_first M J ha)

end Silmaril.Isotope.LetIter.PaperExpression.Source.Freyd.Native.Proofs
