module

public import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.Freyd.Native.Context
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Naturality.Thms

public section

universe u v w u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.Freyd.Native.Proofs

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open LocallyNameless (Tm Derivation)
open Semantics.Categorical
  (TypeModel InstructionModel envObj envSnocIso envPairHom boundVar bind_pre_map pair_pre_map case_pre_map)

local notation "bindArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
local notation "caseArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.caseWithContext

variable {τ : Type u} {Φ : Type v} {ε : Type w} [TypeFormers τ]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) (M : TypeModel τ V) [DistributiveFreydCategory J]

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)
local notation "env" Γ => envObj M Γ₀ (EffectCtx.toBoundCtx Γ)
local notation "input[" Γ "]" => J.map (Iso.hom (packedEnvIso M Γ))

omit [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C] [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C] [DistributiveFreydCategory J] in
private theorem map_square {R S T U : V} {Y : C}
    {p : R ⟶ S} {q : S ⟶ U} {r : R ⟶ T} {s : T ⟶ U}
    (h : p ≫ q = r ≫ s) (b : J.obj U ⟶ Y) :
    J.map p ≫ J.map q ≫ b = J.map r ≫ J.map s ≫ b :=
  (J.map_comp_assoc p q b).symm.trans
    ((congrArg (fun k => J.map k ≫ b) h).trans (J.map_comp_assoc r s b))

private theorem bind_transport {Γ : EffectCtx τ ε} {A B : τ} {e : ε}
    (a : J.obj (env Γ) ⟶ J.obj (M.obj A))
    (b : J.obj (env ((A, e) :: Γ)) ⟶ J.obj (M.obj B)) :
    Freyd.bind J M (X := packType Γ) (A := A) (B := B) (input[Γ] ≫ a) (input[((A, e) :: Γ)] ≫ b) =
      input[Γ] ≫ bindArrow J a (J.map (envSnocIso M Γ₀ Γ.toBoundCtx A).hom ≫ b) := by
  unfold Freyd.bind
  exact (congrArg (bindArrow J (input[Γ] ≫ a))
      (map_square J (packedEnvIso_snoc M Γ A e) b)).trans
    (bind_pre_map J (packedEnvIso M Γ).hom a _)

private theorem bindPair_transport {Γ : EffectCtx τ ε} {A B D : τ} {e : ε}
    (a : J.obj (env Γ) ⟶ J.obj (M.obj (product A B)))
    (b : J.obj (env ((B, e) :: (A, e) :: Γ)) ⟶ J.obj (M.obj D)) :
    Freyd.bindPair J M (X := packType Γ) (A := A) (B := B) (D := D) (input[Γ] ≫ a) (input[((B, e) :: (A, e) :: Γ)] ≫ b) =
      input[Γ] ≫ bindArrow J a (J.map ((env Γ) ◁ (M.productIso A B).hom) ≫
        J.map (envPairHom M Γ₀ Γ.toBoundCtx A B) ≫ b) := by
  unfold Freyd.bindPair
  have changeBody := map_square J (packedEnvIso_pair M Γ A B e) b
  have expand := J.map_comp_assoc ((env Γ) ◁ (M.productIso A B).hom)
    (envPairHom M Γ₀ Γ.toBoundCtx A B) b
  exact (congrArg (bindArrow J (input[Γ] ≫ a))
      (changeBody.trans (congrArg (fun k =>
        J.map ((packedEnvIso M Γ).hom ▷ M.obj (product A B)) ≫ k) expand))).trans
    (bind_pre_map J (packedEnvIso M Γ).hom a _)

private theorem case_transport {Γ : EffectCtx τ ε} {A B D : τ} {e : ε}
    (a : J.obj (env Γ) ⟶ J.obj (M.obj (coprod A B)))
    (l : J.obj (env ((A, e) :: Γ)) ⟶ J.obj (M.obj D))
    (r : J.obj (env ((B, e) :: Γ)) ⟶ J.obj (M.obj D)) :
    Freyd.caseWithContext J M (X := packType Γ) (A := A) (B := B) (D := D) (input[Γ] ≫ a) (input[((A, e) :: Γ)] ≫ l) (input[((B, e) :: Γ)] ≫ r) =
      input[Γ] ≫ caseArrow J (a ≫ J.map (M.coprodIso A B).hom)
        (J.map (envSnocIso M Γ₀ Γ.toBoundCtx A).hom ≫ l)
        (J.map (envSnocIso M Γ₀ Γ.toBoundCtx B).hom ≫ r) := by
  unfold Freyd.caseWithContext
  calc
    _ = caseArrow J (input[Γ] ≫ (a ≫ J.map (M.coprodIso A B).hom))
        (J.map ((packedEnvIso M Γ).hom ▷ M.obj A) ≫ J.map (envSnocIso M Γ₀ Γ.toBoundCtx A).hom ≫ l)
        (J.map ((packedEnvIso M Γ).hom ▷ M.obj B) ≫ J.map (envSnocIso M Γ₀ Γ.toBoundCtx B).hom ≫ r) :=
      congrArg₂ (fun v arms => caseArrow J v arms.1 arms.2) (Category.assoc _ _ _)
        (congrArg₂ Prod.mk (map_square J (packedEnvIso_snoc M Γ A e) l)
          (map_square J (packedEnvIso_snoc M Γ B e) r))
    _ = _ := case_pre_map J (packedEnvIso M Γ).hom _ _ _

variable [HasTy Φ τ] [InstructionModel J M Φ]

private theorem denote_cast {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {A B : τ}
    (d : Derivation Φ Γ₀ β t A) (h : A = B) (free : LoopFree t) :
    denoteLoopFree J M (h ▸ d : Derivation Φ Γ₀ β t B) free =
      denoteLoopFree J M d free ≫ J.map (eqToHom (congrArg M.obj h)) := by
  cases h
  simp

variable [HasEff Φ ε] [Preorder ε] [OrderBot ε]
  {Γ : EffectCtx τ ε} {A : τ} {a : Expr Φ} {e : ε}
  {f : Arrow J M (packType Γ) A}

theorem exists_lowering (h : Denotes J M e Γ A a f) :
    ∃ d : Lowering Γ a A, d.denote J M = f := by
  induction h with
  | @var Γ i hi =>
    have hty := EffectCtx.get_toBoundCtx Γ i
    let d : Derivation Φ Γ₀ Γ.toBoundCtx (.bv i) (Γ.toBoundCtx.get i) := .bv
    refine ⟨⟨.bv i, by simp [Expr.toLetIter, i.isLt], hty ▸ d⟩, ?_⟩
    simp only [Lowering.denote, denote_cast J M, d, denoteLoopFree]
    change input[Γ] ≫ J.map (boundVar M (Γ := Γ₀) (β := Γ.toBoundCtx) i) ≫ J.map (eqToHom (congrArg M.obj hty)) = _
    rw [← J.map_comp_assoc, ← J.map_comp, Category.assoc, packedEnvIso_lookup M Γ i]
  | op hf ha ih =>
    obtain ⟨⟨t, ht, d⟩, rfl⟩ := ih
    refine ⟨⟨.op _ t, by simp [Expr.toLetIter, ht], .op d⟩, ?_⟩
    simp only [Lowering.denote, denoteLoopFree, Freyd.applyInstruction, Category.assoc]
  | let1 ha hb ihA ihB =>
    obtain ⟨⟨a, lowerA, da⟩, rfl⟩ := ihA
    obtain ⟨⟨b, lowerB, db⟩, rfl⟩ := ihB
    refine ⟨⟨.let₁ a b, ?_, .let₁ da db⟩, ?_⟩
    · simp only [Expr.toLetIter, lowerA, Option.bind_some]
      erw [lowerB]
      rfl
    · simp only [Lowering.denote, denoteLoopFree]
      exact (bind_transport J M _ _).symm
  | pair ha hb ihA ihB =>
    obtain ⟨⟨a, lowerA, da⟩, rfl⟩ := ihA
    obtain ⟨⟨b, lowerB, db⟩, rfl⟩ := ihB
    refine ⟨⟨.pair a b, by simp [Expr.toLetIter, lowerA, lowerB], .pair da db⟩, ?_⟩
    simp only [Lowering.denote, denoteLoopFree, Freyd.pair, pair_pre_map, Category.assoc]
  | unit Γ =>
    refine ⟨⟨.unit, rfl, .unit⟩, ?_⟩
    simp only [Lowering.denote, denoteLoopFree, Freyd.toUnit, ← J.map_comp,
      CartesianMonoidalCategory.comp_toUnit_assoc]
  | let2 ha hb ihA ihB =>
    obtain ⟨⟨a, lowerA, da⟩, rfl⟩ := ihA
    obtain ⟨⟨b, lowerB, db⟩, rfl⟩ := ihB
    refine ⟨⟨.let₂ a b, ?_, .let₂ da db⟩, ?_⟩
    · simp only [Expr.toLetIter, lowerA, Option.bind_some]
      erw [lowerB]
      rfl
    · simp only [Lowering.denote, denoteLoopFree, MonoidalCategory.id_tensorHom]
      exact (bindPair_transport J M _ _).symm
  | inl ha ih =>
    obtain ⟨⟨a, lowerA, da⟩, rfl⟩ := ih
    refine ⟨⟨.inl a, by simp [Expr.toLetIter, lowerA], .inl da⟩, ?_⟩
    simp only [Lowering.denote, denoteLoopFree, Freyd.inl, Category.assoc]
  | inr ha ih =>
    obtain ⟨⟨a, lowerA, da⟩, rfl⟩ := ih
    refine ⟨⟨.inr a, by simp [Expr.toLetIter, lowerA], .inr da⟩, ?_⟩
    simp only [Lowering.denote, denoteLoopFree, Freyd.inr, Category.assoc]
  | case ha hl hr ihA ihL ihR =>
    obtain ⟨⟨a, lowerA, da⟩, rfl⟩ := ihA
    obtain ⟨⟨l, lowerL, dl⟩, rfl⟩ := ihL
    obtain ⟨⟨r, lowerR, dr⟩, rfl⟩ := ihR
    refine ⟨⟨.case a l r, ?_, .case da dl dr⟩, ?_⟩
    · simp only [Expr.toLetIter, lowerA, Option.bind_some]
      erw [lowerL]
      simp only [Option.bind_some]
      erw [lowerR]
      rfl
    · simp only [Lowering.denote, denoteLoopFree]
      exact (case_transport J M _ _ _).symm
  | abort ha ih =>
    obtain ⟨⟨a, lowerA, da⟩, rfl⟩ := ih
    refine ⟨⟨.abort a, by simp [Expr.toLetIter, lowerA], .abort da⟩, ?_⟩
    simp only [Lowering.denote, denoteLoopFree, Freyd.abort, Category.assoc]

end Silmaril.Isotope.LetIter.PaperExpression.Source.Freyd.Native.Proofs
