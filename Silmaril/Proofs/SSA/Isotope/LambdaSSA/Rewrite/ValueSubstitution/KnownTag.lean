module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.UnusedSummand.Trim.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Case.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Naturality.Thms

/-! # Remove a known left tag after evaluating its payload -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.KnownTag

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (fst snd)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical
  (TypeModel InstructionModel case_pre_map case_inl_context extend_map extend_postmap)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext extend)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite (SubstDenotes regionDenotes_subst)

local notation "bindRegion" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
local notation "pairMap" => CartesianMonoidalCategory.lift

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C)

variable [DistributiveFreydCategory J] in
private theorem bind_inl_case {E A B P X : V} (unpack : P ≅ A ⨿ B)
    (value : J.obj E ⟶ J.obj A)
    (left : J.obj ((E ⊗ P) ⊗ A) ⟶ J.obj X)
    (right : J.obj ((E ⊗ P) ⊗ B) ⟶ J.obj X) :
    let tagged : A ⟶ P := coprod.inl ≫ unpack.inv
    let input := E ◁ tagged
    bindRegion J (value ≫ J.map tagged)
      (caseWithContext J (J.map (snd E P ≫ unpack.hom)) left right) =
    bindRegion J value (J.map (pairMap input (snd E A)) ≫ left) := by
  dsimp only
  let tagged : A ⟶ P := coprod.inl ≫ unpack.inv
  let input := E ◁ tagged
  have test : input ≫ snd E P ≫ unpack.hom = snd E A ≫ (coprod.inl : A ⟶ A ⨿ B) := by
    simp only [input, CartesianMonoidalCategory.whiskerLeft_snd_assoc, tagged, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  have branchInput :
      pairMap (𝟙 (E ⊗ A)) (snd E A) ≫ (input ▷ A) = pairMap input (snd E A) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  change extend J (value ≫ J.map tagged) ≫
      caseWithContext J (J.map (snd E P ≫ unpack.hom)) left right =
    extend J value ≫ J.map (pairMap input (snd E A)) ≫ left
  rw [extend_postmap, Category.assoc, ← case_pre_map, ← J.map_comp, test, J.map_comp,
    case_inl_context]
  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, extend_map,
    ← J.map_comp_assoc]
  change extend J value ≫ J.map (pairMap (𝟙 (E ⊗ A)) (snd E A) ≫ (input ▷ A)) ≫ left =
    extend J value ≫ J.map (pairMap input (snd E A)) ≫ left
  rw [branchInput]

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]
  {κ : Type u} (M : TypeModel (Ty κ) V) {Φ : Type v} [HasTy Φ (Ty κ)] [InstructionModel J M Φ]

private def supplyTag : Nat → Tm Φ
  | 0 => .var 0
  | 1 => .inl (.var 0)
  | n + 2 => .var (n + 1)

private theorem supplyTag_after_shift (b : Region Φ) :
    (b.renameVars (Silmaril.DeBruijn.lift Nat.succ)).substVars supplyTag = b := by
  rw [Region.substVars_renameVars]
  have vars : supplyTag ∘ Silmaril.DeBruijn.lift Nat.succ = (Tm.var : Nat → Tm Φ) := by
    funext i
    cases i <;> rfl
  rw [vars, Region.substVars_var]

set_option backward.isDefEq.respectTransparency false in
private theorem supplyTag_denotes {Γ : VCtx (Ty κ)} {A B : Ty κ} :
    let E := ctxObj M Γ
    let P := M.obj (Silmaril.coprod A B)
    let tag : M.obj A ⟶ P := coprod.inl ≫ (M.coprodIso A B).inv
    SubstDenotes J M (Φ := Φ) (Γ := A :: Silmaril.coprod A B :: Γ) (Δ := A :: Γ)
      supplyTag (pairMap (E ◁ tag) (snd E (M.obj A))) := by
  intro E P tag i D hit
  cases i with
  | zero =>
      cases Option.some.inj hit
      refine ⟨.var rfl, ?_⟩
      simp only [lookup, CartesianMonoidalCategory.lift_snd]
      exact .var (i := 0) rfl
  | succ i =>
      cases i with
      | zero =>
          cases Option.some.inj hit
          simp only [lookup, CartesianMonoidalCategory.lift_fst_assoc]
          change ∃ ht : Tm.HasType (A :: Γ) (.inl (.var 0)) (Silmaril.coprod A B),
            Denotes J M ht (J.map ((E ◁ tag) ≫ snd E P))
          rw [CartesianMonoidalCategory.whiskerLeft_snd]
          exact ⟨_, by simpa only [tag, J.map_comp, lookup] using
            Denotes.inl (B := B) (Denotes.var (J := J) (M := M) (Φ := Φ)
              (Γ := A :: Γ) (i := 0) (A := A) rfl)⟩
      | succ i =>
          simp only [lookup, CartesianMonoidalCategory.lift_fst_assoc]
          change ∃ ht : Tm.HasType (A :: Γ) (.var (i + 1)) D,
            Denotes J M ht (J.map ((E ◁ tag) ≫ fst E P ≫ lookup M i hit))
          rw [CartesianMonoidalCategory.whiskerLeft_fst_assoc]
          exact ⟨_, by simpa only [lookup] using
            (Denotes.var (J := J) (M := M) (Φ := Φ) (Γ := A :: Γ) (i := i + 1) hit)⟩

set_option backward.isDefEq.respectTransparency false in
theorem let_inl_case {Γ : VCtx (Ty κ)} {L : LCtx (Ty κ)} {a : Tm Φ} {A : Ty κ}
    (determined : TypeDetermined Γ a A) {left right : Region Φ}
    {h : Region.HasType Γ (.let₁ (.inl a)
      (.case (.var 0) (left.renameVars (Silmaril.DeBruijn.lift Nat.succ)) right)) L}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)} (d : RegionDenotes J M h f) :
    ∃ (ha : a.HasType Γ A) (hb : left.HasType (A :: Γ) L),
      RegionDenotes J M (.let₁ ha hb) f := by
  cases d with
  | let₁ dv body =>
      cases dv with
      | inl payload =>
          rename_i D B _ ha _ _
          have fixed := determined D ha
          subst D
          cases body with
          | case test yes no =>
              cases test with
              | var hit =>
                  obtain ⟨rfl, rfl⟩ := Ty.coprod.inj (Option.some.inj hit)
                  have moved := regionDenotes_subst J M yes
                    (supplyTag_denotes J M (Γ := Γ) (A := A) (B := B))
                  rw [supplyTag_after_shift] at moved
                  obtain ⟨hb, selected⟩ := moved
                  refine ⟨ha, hb, ?_⟩
                  simp only [lookup, ← J.map_comp]
                  rw [bind_inl_case]
                  exact .let₁ payload selected

theorem cfg_entry {Γ : VCtx (Ty κ)} {L : LCtx (Ty κ)} {a : Tm Φ} {A : Ty κ}
    (determined : TypeDetermined Γ a A) {left right : Region Φ}
    {n : Nat} {blocks : Fin (n + 1) → Region Φ}
    {h : Region.HasType Γ (.cfg (.let₁ (.inl a)
      (.case (.var 0) (left.renameVars (Silmaril.DeBruijn.lift Nat.succ)) right)) (n + 1) blocks) L}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)} (d : RegionDenotes J M h f) :
    ∃ ht : Region.HasType Γ (.cfg (.let₁ a left) (n + 1) blocks) L, RegionDenotes J M ht f := by
  obtain ⟨S, _, hb, entry, rows, joint, de, db, dc, rfl⟩ := d.cfg_readback J M
  obtain ⟨ha, hl, de'⟩ := let_inl_case J M determined de
  exact ⟨.cfg S (.let₁ ha hl) hb, RegionDenotes.cfg (.let₁ ha hl) hb de' db dc⟩

theorem cfg_agree {Γ : VCtx (Ty κ)} {L : LCtx (Ty κ)} {a : Tm Φ} {A : Ty κ}
    {left right right' : Region Φ} {n : Nat} {P : Fin (n + 1) → Ty κ}
    {blocks : Fin (n + 1) → Region Φ} {tag : Bool}
    (p : UnusedSummand.Program (Φ := Φ) P L Γ) (roll : IterationRolling C)
    (determined : TypeDetermined Γ a A)
    (shape : p.region tag = .cfg (.let₁ a left) (n + 1) blocks)
    {h : Region.HasType Γ (.cfg (.let₁ (.inl a)
      (.case (.var 0) (left.renameVars (Silmaril.DeBruijn.lift Nat.succ)) right)) (n + 1) blocks) L}
    {h' : Region.HasType Γ (.cfg (.let₁ (.inl a)
      (.case (.var 0) (left.renameVars (Silmaril.DeBruijn.lift Nat.succ)) right')) (n + 1) blocks) L}
    {f g : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}
    (d : RegionDenotes J M h f) (e : RegionDenotes J M h' g) : f = g := by
  have leftResult : ∃ t : (p.region tag).HasType Γ L, RegionDenotes J M t f := by
    rw [shape]
    exact cfg_entry J M determined d
  have rightResult : ∃ t : (p.region tag).HasType Γ L, RegionDenotes J M t g := by
    rw [shape]
    exact cfg_entry J M determined e
  obtain ⟨_, d'⟩ := leftResult
  obtain ⟨_, e'⟩ := rightResult
  exact p.denotes_eq_trimmed J M roll d' e'

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.KnownTag
