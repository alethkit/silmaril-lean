module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Direct.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Assembly.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Thms

/-! # Shared denotational congruence for typed Paper rewrite relations -/

public section

universe v₁ v₂ u₁ u₂ u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type v} [HasTy Φ τ] [InstructionModel J M Φ]

/-- The two regions admit the same arrow in the structural denotation graph. -/
@[expose] def CommonDenotation (Γ : VCtx τ) (r s : Region Φ) (L : LCtx τ) : Prop :=
  ∃ (hr : HasType Γ r L) (hs : HasType Γ s L), ∃ f,
    RegionDenotes J M hr f ∧ RegionDenotes J M hs f

namespace CommonDenotation

variable {J M} {Γ Δ : VCtx τ} {L K : LCtx τ} {r s t : Region Φ}

theorem of_eq {hr : HasType Γ r L} {hs : HasType Γ s L}
    (h : denoteRegion J M hr = denoteRegion J M hs) : CommonDenotation J M Γ r s L :=
  ⟨hr, hs, _, denoteRegion_spec J M hr, h.symm ▸ denoteRegion_spec J M hs⟩

theorem eq_denote [RegionTypingCoherent (Φ := Φ) J M]
    (h : CommonDenotation J M Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs := by
  obtain ⟨_, _, _, dr, ds⟩ := h
  exact (dr.eq_denote J M).symm.trans (ds.eq_denote J M)

theorem symm (h : CommonDenotation J M Γ r s L) : CommonDenotation J M Γ s r L := by
  obtain ⟨hr, hs, f, dr, ds⟩ := h
  exact ⟨hs, hr, f, ds, dr⟩

theorem trans [RegionTypingCoherent (Φ := Φ) J M]
    (h : CommonDenotation J M Γ r s L) (k : CommonDenotation J M Γ s t L) :
    CommonDenotation J M Γ r t L := by
  obtain ⟨hr, hm, f, dr, dm⟩ := h
  obtain ⟨_, ht, g, dm', dt⟩ := k
  have eq : f = g := RegionTypingCoherent.denotes_eq (h := hm) dm dm'
  exact ⟨hr, ht, g, eq ▸ dr, dt⟩

theorem let₁ {A : τ} {a : Tm Φ} (ha : Tm.HasType Γ a A)
    (h : CommonDenotation J M (A :: Γ) r s L) :
    CommonDenotation J M Γ (.let₁ a r) (.let₁ a s) L := by
  obtain ⟨hr, hs, _, dr, ds⟩ := h
  let da := denote_spec J M ha
  exact ⟨.let₁ ha hr, .let₁ ha hs, _, .let₁ da dr, .let₁ da ds⟩

theorem let₂ {A B : τ} {a : Tm Φ} (ha : Tm.HasType Γ a (product A B))
    (h : CommonDenotation J M (B :: A :: Γ) r s L) :
    CommonDenotation J M Γ (.let₂ a r) (.let₂ a s) L := by
  obtain ⟨hr, hs, _, dr, ds⟩ := h
  let da := denote_spec J M ha
  exact ⟨.let₂ ha hr, .let₂ ha hs, _, .let₂ da dr, .let₂ da ds⟩

theorem case {A B : τ} {a : Tm Φ} {l l' r r' : Region Φ}
    (ha : Tm.HasType Γ a (Silmaril.coprod A B)) (hl : CommonDenotation J M (A :: Γ) l l' L)
    (hr : CommonDenotation J M (B :: Γ) r r' L) :
    CommonDenotation J M Γ (.case a l r) (.case a l' r') L := by
  obtain ⟨hl, hl', _, dl, dl'⟩ := hl
  obtain ⟨hr, hr', _, dr, dr'⟩ := hr
  let da := denote_spec J M ha
  exact ⟨.case ha hl hr, .case ha hl' hr', _, .case da dl dr, .case da dl' dr'⟩

theorem cfg {n : Nat} {bs bs' : Fin n → Region Φ} (R : Fin n → τ)
    (he : CommonDenotation J M Γ r s (List.ofFn R ++ L))
    (hb : ∀ i, CommonDenotation J M (R i :: Γ) (bs i) (bs' i) (List.ofFn R ++ L)) :
    CommonDenotation J M Γ (.cfg r n bs) (.cfg s n bs') L := by
  obtain ⟨he, he', f, de, de'⟩ := he
  choose hb hb' fb db using hb
  cases n with
  | zero =>
    exact ⟨.cfg R he hb, .cfg R he' hb', f, .cfgZero he hb de, .cfgZero he' hb' de'⟩
  | succ n =>
    obtain ⟨_, dc⟩ := collectiveDenotes_exists_succ J M n _ R _ fb
    exact ⟨.cfg R he hb, .cfg R he' hb', _,
      .cfg he hb de (fun i => (db i).1) dc, .cfg he' hb' de' (fun i => (db i).2) dc⟩

theorem substVars {θ : Nat → Tm Φ}
    (h : CommonDenotation J M Γ r s L)
    (hθ : ∀ ⦃i A⦄, At Γ i A → Tm.BranchValue Δ (θ i) A) :
    CommonDenotation J M Δ (r.substVars θ) (s.substVars θ) L := by
  obtain ⟨_, _, f, dr, ds⟩ := h
  obtain ⟨k, transport⟩ := RegionDenotes.substBranchValues J M hθ
  obtain ⟨hr, dr'⟩ := transport dr
  obtain ⟨hs, ds'⟩ := transport ds
  exact ⟨hr, hs, J.map k ≫ f, dr', ds'⟩

theorem renameLabels {ρ : Nat → Nat}
    (h : CommonDenotation J M Γ r s L) (hρ : Ren L K ρ) :
    CommonDenotation J M Γ (r.renameLabels ρ) (s.renameLabels ρ) K := by
  obtain ⟨_, _, _, dr, ds⟩ := h
  exact ⟨_, _, _, dr.renameLabels J M hρ, ds.renameLabels J M hρ⟩

variable [FreydCategory.CentralUnit J] [RegionTypingCoherent (Φ := Φ) J M]

set_option backward.isDefEq.respectTransparency false in
theorem lsubstCongr
    (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
      Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)
    {σ υ : Nat → Region Φ} {p : Region Φ} (hp : ValueBranches Γ p L)
    (h : ∀ ⦃i A⦄, At L i A → CommonDenotation J M (A :: Γ) (σ i) (υ i) K) :
    CommonDenotation J M Γ (p.lsubst σ) (p.lsubst υ) K := by
  have hσ : LSubst.HasType Γ L K σ := fun _ _ hi => by
    obtain ⟨hr, _, _, _, _⟩ := h hi
    exact hr
  have hυ : LSubst.HasType Γ L K υ := fun _ _ hi => by
    obtain ⟨_, hs, _, _, _⟩ := h hi
    exact hs
  obtain ⟨k, dk⟩ := ContinuationDenotes.exists_of_typed M J hσ
  have dk' : ContinuationDenotes J M υ k := by
    intro i A hi
    obtain ⟨_, ds⟩ := dk hi
    obtain ⟨_, ht, _, ds', dt⟩ := h hi
    exact ⟨ht, RegionTypingCoherent.denotes_eq ds' ds ▸ dt⟩
  exact of_eq ((denoteRegion_lsubst_sharedTensor J M shared hp.hasType
    (hp.hasType.lsubst hσ) (PureBranches.of_valueBranches J M hp) dk).trans
    (denoteRegion_lsubst_sharedTensor J M shared hp.hasType
      (hp.hasType.lsubst hυ) (PureBranches.of_valueBranches J M hp) dk').symm)

set_option backward.isDefEq.respectTransparency false in
theorem lsubstPost
    (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
      Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)
    {σ : Nat → Region Φ} (h : CommonDenotation J M Γ r s L)
    (hr : ValueBranches Γ r L) (hs : ValueBranches Γ s L) (hσ : LSubst.HasType Γ L K σ) :
    CommonDenotation J M Γ (r.lsubst σ) (s.lsubst σ) K := by
  obtain ⟨_, dk⟩ := ContinuationDenotes.exists_of_typed M J hσ
  apply of_eq (hr := hr.hasType.lsubst hσ) (hs := hs.hasType.lsubst hσ)
  rw [denoteRegion_lsubst_sharedTensor J M shared hr.hasType _ (PureBranches.of_valueBranches J M hr) dk,
    denoteRegion_lsubst_sharedTensor J M shared hs.hasType _ (PureBranches.of_valueBranches J M hs) dk,
    h.eq_denote hr.hasType hs.hasType]

end CommonDenotation

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper
