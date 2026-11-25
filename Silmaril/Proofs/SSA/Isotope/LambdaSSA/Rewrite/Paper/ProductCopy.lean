module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Copy.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Thms

/-! # Copying constructor returns and their sequential composites -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductCopy

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.TypeCategory
open CfgEta.TypeCategory
  (whiskerLeftRegion whiskerRightRegion whiskerLeftRegion_typed whiskerRightRegion_typed
    whiskerLeftBody whiskerRightBody)
open Paper (Eqv)
open CategoryTheory
open Silmaril.DeBruijn (lift)

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
local notation "obj" => Paper.TypeCategory.ofType (Φ := Φ)

private abbrev seq (r s : Region Φ) : Region Φ := compLSubst (fun _ => r) (fun _ => s) 0

private theorem seqBranches {X A B : τ} {r s : Region Φ}
    (hr : ValueBranches [X] r [A]) (hs : ValueBranches [A] s [B]) :
    ValueBranches [X] (seq r s) [B] :=
  have left : LSubst.ValueFamily [] [X] [A] (fun _ => r) :=
    fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ hr
  have right : LSubst.ValueFamily [] [A] [B] (fun _ => s) :=
    fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ hs
  (left.comp right) (ℓ := 0) rfl

private abbrev leftRen : Nat → Nat := lift (Nat.succ ∘ Nat.succ)
private abbrev rightRen : Nat → Nat := Nat.succ ∘ lift Nat.succ
private abbrev unpack (l r : Tm Φ) := Tm.consSubst r (Tm.singleSubst l)

private theorem pair_then_whiskerRight (l r a : Tm Φ) :
    seq (.br 0 (.pair l r)) (whiskerRightRegion (.br 0 a)) =
      .let₂ (.pair l r) (.br 0 (.pair (a.rename rightRen) (.var 0))) := by
  simp only [seq, compLSubst, whiskerRightRegion, whiskerRightBody, lsubst, renameVars, substVars,
    liftLSubstVars, Tm.rename, Tm.subst, Tm.subst_rename, Tm.singleSubst, Tm.consSubst]
  congr 3
  rw [Tm.rename_eq_subst]
  congr 1
  funext i
  cases i <;> rfl

private theorem pair_then_whiskerLeft (l r b : Tm Φ) :
    seq (.br 0 (.pair l r)) (whiskerLeftRegion (.br 0 b)) =
      .let₂ (.pair l r) (.br 0 (.pair (.var 1) (b.rename leftRen))) := by
  simp only [seq, compLSubst, whiskerLeftRegion, whiskerLeftBody, lsubst, renameVars, substVars,
    liftLSubstVars, Tm.rename, Tm.subst, Tm.subst_rename, Tm.singleSubst, Tm.consSubst]
  congr 3
  rw [Tm.rename_eq_subst]
  congr 1
  funext i
  cases i <;> rfl

private theorem right_whisker_on_duplicate {X A : τ} {a : Tm Φ} (ha : Tm.BranchValue [X] a A) :
    Eqv [X] (seq (Paper.RetainedLet.diagonal : Region Φ) (whiskerRightRegion (.br 0 a)))
      (.br 0 (.pair a (.var 0))) [product A X] := by
  change Eqv [X] (seq (.br 0 (.pair (.var 0) (.var 0))) (whiskerRightRegion (.br 0 a))) _ _
  rw [pair_then_whiskerRight]
  have renameA : Ren [X] [X, X, X] rightRen :=
    ((Ren.wk [] X).lift X).comp (Ren.wk [X, X] X)
  have eq : (a.rename rightRen).subst (unpack (.var 0) (.var 0)) = a := by
    rw [Tm.subst_rename]
    conv_rhs => rw [← Tm.subst_var a]
    apply Paper.RetainedLet.term_subst_eq ha.hasType
    intro i T hi
    cases i with
    | zero => rfl
    | succ i => simp [At] at hi
  have x : Tm.BranchValue [X] (.var 0 : Tm Φ) X := .var rfl
  have beta := Eqv.productBeta (.let₂Beta x x
    (.br (ℓ := 0) (L := [product A X]) rfl (.pair (ha.hasType.rename renameA) (.var (i := 0) rfl))))
  change Eqv [X] _ (.br 0 (.pair ((a.rename rightRen).subst (unpack (.var 0) (.var 0))) (.var 0))) _ at beta
  simpa only [eq] using beta

private theorem left_whisker_on_retained {X A B : τ} {a b : Tm Φ}
    (ha : Tm.BranchValue [X] a A) (hb : Tm.BranchValue [X] b B) :
    Eqv [X] (seq (.br 0 (.pair a (.var 0))) (whiskerLeftRegion (.br 0 b)))
      (.br 0 (.pair a b)) [product A B] := by
  rw [pair_then_whiskerLeft]
  have renameB : Ren [X] [X, A, X] leftRen :=
    ((Ren.wk [] X).comp (Ren.wk [X] A)).lift X
  have eq : (b.rename leftRen).subst (unpack a (.var 0)) = b := by
    rw [Tm.subst_rename]
    conv_rhs => rw [← Tm.subst_var b]
    apply Paper.RetainedLet.term_subst_eq hb.hasType
    intro i T hi
    cases i with
    | zero => rfl
    | succ i => simp [At] at hi
  have x : Tm.BranchValue [X] (.var 0 : Tm Φ) X := .var rfl
  have beta := Eqv.productBeta (.let₂Beta ha x
    (.br (ℓ := 0) (L := [product A B]) rfl (.pair (.var (i := 1) rfl) (hb.hasType.rename renameB))))
  change Eqv [X] _ (.br 0 (.pair a ((b.rename leftRen).subst (unpack a (.var 0))))) _ at beta
  simpa only [eq] using beta

set_option backward.isDefEq.respectTransparency false in
theorem pairArrows_branchValue {X A B : τ} {a b : Tm Φ}
    (ha : Tm.BranchValue [X] a A) (hb : Tm.BranchValue [X] b B) :
    pairArrows (ofRegion (.br (ℓ := 0) rfl ha)) (ofRegion (.br (ℓ := 0) rfl hb)) =
      ofRegion (.br (ℓ := 0) rfl (.pair ha hb)) := by
  have x : Tm.BranchValue [X] (.var 0 : Tm Φ) X := .var rfl
  have a : ValueBranches [X] (.br 0 a) [A] := .br rfl ha
  have b : ValueBranches [X] (.br 0 b) [B] := .br rfl hb
  have ax : ValueBranches [X] (.br 0 (.pair _ (.var 0))) [product A X] := .br rfl (.pair ha x)
  unfold pairArrows diagonalArrow
  rw [whiskerRight_ofRegion, whiskerLeft_ofRegion, ← Category.assoc]
  unfold tensorObj
  rw [ofRegion_comp _ _ (seqBranches (Paper.RetainedLet.diagonal_typed X) (whiskerRightRegion_typed X a))]
  rw [(ofRegion_eq_iff _ ax).mpr (right_whisker_on_duplicate ha)]
  rw [ofRegion_comp _ _ (seqBranches ax (whiskerLeftRegion_typed A b))]
  exact (ofRegion_eq_iff _ _).mpr (left_whisker_on_retained ha hb)

theorem pairArrows_copy_branchValue {X A : τ} {a : Tm Φ} (ha : Tm.BranchValue [X] a A) :
    pairArrows (ofRegion (.br (ℓ := 0) rfl ha)) (ofRegion (.br (ℓ := 0) rfl ha)) =
      ofRegion (.br (ℓ := 0) rfl ha) ≫ diagonalArrow A := by
  rw [pairArrows_branchValue ha ha]
  rfl


set_option backward.isDefEq.respectTransparency false in
theorem pairArrows_copy_comp {X A B : τ} (f : obj X ⟶ obj A) (g : obj A ⟶ obj B)
    (central : WhiskerCentral f) (hf : pairArrows f f = f ≫ diagonalArrow A)
    (hg : pairArrows g g = g ≫ diagonalArrow B) :
    pairArrows (f ≫ g) (f ≫ g) = (f ≫ g) ≫ diagonalArrow B := by
  calc
    _ = pairArrows f f ≫ (whiskerRight g (obj A) ≫ whiskerLeft (obj B) g) := by
      simp only [pairArrows, whiskerRight_comp, whiskerLeft_comp, Category.assoc]
      rw [← Category.assoc (whiskerRight g (obj X)), ← (central g).2, Category.assoc]
    _ = f ≫ pairArrows g g := by rw [hf, Category.assoc]; rfl
    _ = _ := by rw [hg, Category.assoc]

theorem pairArrows_copy_returnTerm_branchValue {X A : τ} {a : Tm Φ} (ha : Tm.BranchValue [X] a A) :
    pairArrows (returnTerm ha.hasType) (returnTerm ha.hasType) = returnTerm ha.hasType ≫ diagonalArrow A := by
  have h : returnTerm ha.hasType = ofRegion (.br (ℓ := 0) rfl ha) :=
    (ofRegion_eq_iff _ _).mpr (.cfgEta (.native (.base (CfgEta.TypeCategory.returnRegion_branchValue ha))))
  rw [h]
  exact pairArrows_copy_branchValue ha

local notation "Comp" => Paper.TypeCategory (τ := τ) Φ

local instance : (CentralCopies (τ := τ) (Φ := Φ)).IsMultiplicative where
  id_mem X := by
    change WhiskerCentral (𝟙 X) ∧ pairArrows (τ := τ) (𝟙 X) (𝟙 X) = (𝟙 X) ≫ diagonalArrow (show τ from X)
    refine ⟨WhiskerCentral.id X, ?_⟩
    rw [← ofRegion_id (show τ from X)]
    exact pairArrows_copy_branchValue (Tm.BranchValue.var (i := 0) rfl)
  comp_mem f g hf hg :=
    ⟨WhiskerCentral.comp hf.1 hg.1, pairArrows_copy_comp (τ := τ) f g hf.1 hf.2 hg.2⟩

theorem primitiveReturnsCopy_iff_generated {ε : Type w} [HasEff Φ ε] (pe : ε)
    (central : PrimitiveReturnsCentral (τ := τ) (Φ := Φ) pe) :
    PrimitiveReturnsCopy (τ := τ) (Φ := Φ) pe ↔
      (PureReturnGenerators (τ := τ) (Φ := Φ) pe).multiplicativeClosure ≤ CentralCopies := by
  constructor
  · intro copy
    refine (MorphismProperty.multiplicativeClosure_le_iff _ _).mpr ?_
    intro X A f hf
    rcases hf with ⟨a, ha, rfl⟩ | ⟨p, h, hp, rfl⟩
    · exact ⟨whiskerCentral_returnRegion_branchValue ha, pairArrows_copy_returnTerm_branchValue ha⟩
    · cases h with
      | op h =>
        cases h with
        | var hi =>
          cases Option.some.inj hi
          exact ⟨central p hp, copy p hp⟩
  · intro h p hp
    exact (h _ (.of _ (.inr ⟨p, .op (.var rfl), hp, rfl⟩))).2

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductCopy
