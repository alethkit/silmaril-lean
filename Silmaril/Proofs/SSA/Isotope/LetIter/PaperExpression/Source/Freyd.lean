module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Freyd.Defs

public section

universe u v w u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.Freyd.Proofs

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

theorem wf (h : Denotes J M e Γ A a f) : Wf Γ a A e := by
  induction h with
  | var i hi => exact .var i hi
  | op hf _ ih => exact .op hf ih
  | let1 _ _ ih₁ ih₂ => exact .let₁ ih₁ ih₂
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | unit Γ => exact .unit Γ e
  | let2 _ _ ih₁ ih₂ => exact .let₂ ih₁ ih₂
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ih₁ ih₂ ih₃ => exact .case ih₁ ih₂ ih₃
  | abort _ ih => exact .abort ih

theorem exists_denotes (h : Wf Γ a A e) : ∃ f, Denotes J M e Γ A a f := by
  induction h with
  | var i hi => exact ⟨_, .var i hi⟩
  | op hf _ ih =>
    obtain ⟨_, ha⟩ := ih
    exact ⟨_, .op hf ha⟩
  | let₁ _ _ ih₁ ih₂ =>
    obtain ⟨_, ha⟩ := ih₁
    obtain ⟨_, hb⟩ := ih₂
    exact ⟨_, .let1 ha hb⟩
  | pair _ _ ih₁ ih₂ =>
    obtain ⟨_, ha⟩ := ih₁
    obtain ⟨_, hb⟩ := ih₂
    exact ⟨_, .pair ha hb⟩
  | unit Γ _ => exact ⟨_, .unit Γ⟩
  | let₂ _ _ ih₁ ih₂ =>
    obtain ⟨_, ha⟩ := ih₁
    obtain ⟨_, hb⟩ := ih₂
    exact ⟨_, .let2 ha hb⟩
  | inl _ ih =>
    obtain ⟨_, ha⟩ := ih
    exact ⟨_, .inl ha⟩
  | inr _ ih =>
    obtain ⟨_, ha⟩ := ih
    exact ⟨_, .inr ha⟩
  | case _ _ _ ih₁ ih₂ ih₃ =>
    obtain ⟨_, ha⟩ := ih₁
    obtain ⟨_, hl⟩ := ih₂
    obtain ⟨_, hr⟩ := ih₃
    exact ⟨_, .case ha hl hr⟩
  | abort _ ih =>
    obtain ⟨_, ha⟩ := ih
    exact ⟨_, .abort ha⟩

theorem map_denote (F : Comparison J M Φ e) (h : Denotes J M e Γ A a f) :
    F.map (Source.denote ⟨a, wf h⟩) = f := by
  induction h with
  | var i hi => exact (congrArg F.map (Source.denote_var i hi)).trans (F.map_projection _ i)
  | op hf ha ih =>
    rw [Source.denote_op hf ⟨_, wf ha⟩, F.map_instruction, ih]
  | let1 ha hb ihA ihB =>
    exact (congrArg F.map (Source.denote_let1 ⟨_, wf ha⟩ ⟨_, wf hb⟩)).trans
      ((F.map_bind _ _).trans (congrArg₂ (bind J M) ihA ihB))
  | pair ha hb ihA ihB =>
    rw [Source.denote_pair ⟨_, wf ha⟩ ⟨_, wf hb⟩, F.map_pair, ihA, ihB]
  | unit Γ =>
    rw [Source.denote_unit, F.map_unit]
  | let2 ha hb ihA ihB =>
    exact (congrArg F.map (Source.denote_let2 ⟨_, wf ha⟩ ⟨_, wf hb⟩)).trans
      ((F.map_bindPair _ _).trans (congrArg₂ (bindPair J M) ihA ihB))
  | inl ha ih =>
    rw [Source.denote_inl ⟨_, wf ha⟩, F.map_inl, ih]
  | inr ha ih =>
    rw [Source.denote_inr ⟨_, wf ha⟩, F.map_inr, ih]
  | case ha hl hr ihA ihL ihR =>
    exact (congrArg F.map (Source.denote_case ⟨_, wf ha⟩ ⟨_, wf hl⟩ ⟨_, wf hr⟩)).trans
      ((F.map_case _ _ _).trans (congrArg₂ (fun v branches => caseWithContext J M v branches.1 branches.2)
        ihA (congrArg₂ Prod.mk ihL ihR)))
  | abort ha ih =>
    rw [Source.denote_abort ⟨_, wf ha⟩, F.map_abort, ih]

theorem denotes_iff (F : Comparison J M Φ e) (a : TypedExpr Φ Γ A e) :
    Denotes J M e Γ A a.val f ↔ F.map (Source.denote a) = f := by
  constructor
  · intro h
    exact map_denote F h
  · intro h
    obtain ⟨g, hg⟩ := exists_denotes (J := J) (M := M) a.prop
    exact (map_denote F hg).symm.trans h ▸ hg

end Silmaril.Isotope.LetIter.PaperExpression.Source.Freyd.Proofs
