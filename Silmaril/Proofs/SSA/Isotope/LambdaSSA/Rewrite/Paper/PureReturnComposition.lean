module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Defs

/-! # Typed return composition and interchange -/

public section

universe u v w

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PureReturnComposition

open CategoryTheory Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Region.Paper (TypeCategory)
open Region.Paper.TypeCategory
open Region.CfgEta.TypeCategory (returnRegion returnRegion_typed returnRegion_rename)
open Silmaril.DeBruijn (lift)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Comp" => TypeCategory (τ := τ) Φ

theorem returnTerm_comp {A B C : τ} {a b : Tm Φ}
    (ha : Tm.HasType [A] a B) (hb : Tm.HasType [B] b C) :
    returnTerm ha ≫ returnTerm hb =
      returnTerm (.let₁ ha (hb.rename ((Ren.wk [] A).lift B))) := by
  unfold returnTerm
  have h := Tm.HasType.let₁ ha (hb.rename ((Ren.wk [] A).lift B))
  have eq : returnRegion (.let₁ a (b.rename (lift Nat.succ))) =
      compLSubst (fun _ => returnRegion a) (fun _ => returnRegion b) 0 := by
    simp only [returnRegion, returnRegion_rename]
    rfl
  rw [ofRegion_comp _ _ (eq ▸ returnRegion_typed h)]
  apply (ofRegion_eq_iff _ _).mpr
  rw [← eq]
  exact Paper.Eqv.refl (returnRegion_typed h).hasType

theorem returnTerm_op_branchValue {A : τ} {a : Tm Φ} (f : Φ)
    (ha : Tm.BranchValue [A] a (instrSrc f)) :
    returnTerm (.op (f := f) ha.hasType) = returnTerm ha.hasType ≫ primitiveReturn f := by
  unfold returnTerm primitiveReturn
  have branch : ValueBranches [A] (.br 0 a) [instrSrc f] := .br rfl ha
  rw [(ofRegion_eq_iff (returnRegion_typed ha.hasType) branch).mpr
    (.cfgEta (.native (.base (CfgEta.TypeCategory.returnRegion_branchValue ha))))]
  have primitive : Tm.HasType [instrSrc (τ := τ) f] (.op f (.var 0)) (instrTrg f) :=
    .op (.var rfl)
  exact (ofRegion_comp branch (returnRegion_typed primitive)
    (returnRegion_typed (.op (f := f) ha.hasType))).symm

theorem interchange_left_comp {A B C X Y : Comp} {f : A ⟶ B} {g : B ⟶ C} {k : X ⟶ Y}
    (hf : whiskerRight f X ≫ whiskerLeft B k = whiskerLeft A k ≫ whiskerRight f Y)
    (hg : whiskerRight g X ≫ whiskerLeft C k = whiskerLeft B k ≫ whiskerRight g Y) :
    whiskerRight (f ≫ g) X ≫ whiskerLeft C k =
      whiskerLeft A k ≫ whiskerRight (f ≫ g) Y := by
  rw [whiskerRight_comp, whiskerRight_comp, Category.assoc, hg, ← Category.assoc, hf, Category.assoc]

theorem interchange_right_comp {A B C X Y : Comp} {f : A ⟶ B} {g : B ⟶ C} {k : X ⟶ Y}
    (hf : whiskerLeft X f ≫ whiskerRight k B = whiskerRight k A ≫ whiskerLeft Y f)
    (hg : whiskerLeft X g ≫ whiskerRight k C = whiskerRight k B ≫ whiskerLeft Y g) :
    whiskerLeft X (f ≫ g) ≫ whiskerRight k C =
      whiskerRight k A ≫ whiskerLeft Y (f ≫ g) := by
  rw [whiskerLeft_comp, whiskerLeft_comp, Category.assoc, hg, ← Category.assoc, hf, Category.assoc]

theorem returnTerm_id (A : τ) :
    returnTerm (Φ := Φ) (.var (i := 0) (show At [A] 0 A from rfl)) = 𝟙 (ofType A) := by
  unfold returnTerm
  refine ((ofRegion_eq_iff _ _).mpr ?_).trans (ofRegion_id A)
  exact .cfgEta (.native (.base (CfgEta.TypeCategory.returnRegion_branchValue (.var rfl))))

variable {ε : Type w} [HasEff Φ ε] (pe : ε)

omit [HasTy Φ τ] in
private theorem branchValue_pure {Γ : VCtx τ} {T : τ} {a : Tm Φ}
    (h : Tm.BranchValue Γ a T) : Tm.Pure pe a := by
  induction h with
  | var => exact .var
  | unit => exact .unit
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih

theorem pureReturnGenerators_le (central : PrimitiveReturnsCentral (τ := τ) (Φ := Φ) pe) :
    PureReturnGenerators (τ := τ) (Φ := Φ) pe ≤ CentralPureReturn pe := by
  intro A B f hf
  rcases hf with ⟨a, h, rfl⟩ | ⟨p, h, hp, rfl⟩
  · exact ⟨⟨a, h.hasType, branchValue_pure pe h, rfl⟩, whiskerCentral_returnRegion_branchValue h⟩
  · refine ⟨⟨_, h, .op hp .var, rfl⟩, ?_⟩
    cases h with
    | op h =>
      cases h with
      | var h =>
        cases Option.some.inj h
        exact central p hp

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PureReturnComposition
