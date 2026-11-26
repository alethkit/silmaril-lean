module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Discard.Coproducts.Defs
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.DiscardPreservingCoproducts

/-! # Initiality and binary coproducts of discard-preserving values -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ValueCoproducts

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory CategoryTheory.Limits

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop) (pe : ε)

set_option hygiene false in
local notation "Q" => TypeCategory Seed
set_option hygiene false in
local notation "V" => DiscardPreservingValueCategory Seed pe
set_option hygiene false in
local notation "J" => wideSubcategoryInclusion (DiscardPreservingReturn Seed pe)
set_option hygiene false in
local notation "Obj" => ofType (Φ := Φ) Seed

open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

/-- Computations out of the guarded empty type commute with computations and preserve copy. -/
theorem empty_centralCopies {D : Q} (f : Obj (Silmaril.empty : τ) ⟶ D) : CentralCopies Seed f :=
  DiscardPreservingCoproducts.empty_centralCopies Seed f

/-- Every computation out of the exact empty type is a discard-preserving value. -/
theorem empty_mem {D : Q} (f : Obj (Silmaril.empty : τ) ⟶ D) :
    DiscardPreservingReturn Seed pe f :=
  DiscardPreservingCoproducts.empty_mem Seed pe f

/-- The same guarded empty object is initial in the value category. -/
noncomputable def valueEmptyIsInitial :
    IsInitial (⟨Obj (Silmaril.empty : τ)⟩ : V) :=
  DiscardPreservingCoproducts.valueEmptyIsInitial Seed pe

instance valueHasInitial : HasInitial V :=
  (valueEmptyIsInitial Seed pe).hasInitial

/-- The value inclusion preserves the initial object unconditionally. -/
instance valuePreservesInitial : PreservesColimit (Functor.empty.{0} V) (J) :=
  DiscardPreservingCoproducts.valuePreservesInitial Seed pe

/-- Copairing exact Paper sums preserves centrality and copying. -/
theorem centralCopies_exactCopair {A B D : τ}
    {f : Paper.TypeCategory.ofType (Φ := Φ) A ⟶ Paper.TypeCategory.ofType D}
    {g : Paper.TypeCategory.ofType (Φ := Φ) B ⟶ Paper.TypeCategory.ofType D}
    (hf : Paper.TypeCategory.CentralCopies f) (hg : Paper.TypeCategory.CentralCopies g) :
    Paper.TypeCategory.CentralCopies
      ((Paper.TypeCategory.sumIso A B).hom ≫ coprod.desc f g) :=
  DiscardPreservingCoproducts.copair_copies hf hg

/-- The computation copair already has a copying lift and preserves discard.
A pure-return representative is the sole additional requirement for value membership. -/
theorem exactCopair_mem_iff {A B : τ} {D : Q} {f : Obj A ⟶ D} {g : Obj B ⟶ D}
    (hf : DiscardPreservingReturn Seed pe f) (hg : DiscardPreservingReturn Seed pe g) :
    DiscardPreservingReturn Seed pe (exactCopair Seed f g) ↔
      ProjectedPureReturn Seed pe (exactCopair Seed f g) :=
  DiscardPreservingCoproducts.exactCopair_mem_iff Seed pe hf hg

/-- The left syntax injection is a discard-preserving value. -/
theorem sum_inl_mem (A B : τ) : DiscardPreservingReturn Seed pe (sumCofan Seed A B).inl :=
  DiscardPreservingCoproducts.inl_mem Seed pe A B

/-- The right syntax injection is a discard-preserving value. -/
theorem sum_inr_mem (A B : τ) : DiscardPreservingReturn Seed pe (sumCofan Seed A B).inr :=
  DiscardPreservingCoproducts.inr_mem Seed pe A B

/-- The syntax sum cocone with its two constructor-valued injections. -/
@[expose] def valueSumCofan (A B : τ) : BinaryCofan (⟨Obj A⟩ : V) (⟨Obj B⟩ : V) :=
  BinaryCofan.mk (P := (⟨Obj (Silmaril.coprod A B)⟩ : V))
    ⟨(sumCofan Seed A B).inl, sum_inl_mem Seed pe A B⟩
    ⟨(sumCofan Seed A B).inr, sum_inr_mem Seed pe A B⟩

/-- The syntax sum is a value coproduct under pure copair closure. -/
noncomputable def valueSumIsColimit (h : CopairPure Seed pe) (A B : τ) :
    IsColimit (valueSumCofan Seed pe A B) :=
  DiscardPreservingCoproducts.valueSumIsColimit Seed pe h A B

/-- The two constructor injections are coproduct injections exactly when pure copair closure holds. -/
theorem copairPure_iff_valueSums : CopairPure Seed pe ↔
    ∀ A B : τ, Nonempty (IsColimit (valueSumCofan Seed pe A B)) :=
  DiscardPreservingCoproducts.copairPure_iff_valueSums Seed pe

/-- The typed case-return equation constructs a pure representative by case analysis. -/
theorem copairPure_of_caseReturn (h : CaseReturnAgreement Seed pe) : CopairPure Seed pe :=
  DiscardPreservingCoproducts.copairPure_of_caseReturn Seed pe h

/-- Supply the value-side finite coproduct instance using the pure copair law. -/
theorem valueHasFiniteCoproducts (h : CopairPure Seed pe) : HasFiniteCoproducts V :=
  DiscardPreservingCoproducts.valueHasFiniteCoproducts Seed pe h

/-- With the same law, the value inclusion preserves the finite coproducts. -/
theorem valuePreservesFiniteCoproducts (h : CopairPure Seed pe) : PreservesFiniteCoproducts (J) :=
  DiscardPreservingCoproducts.valuePreservesFiniteCoproducts Seed pe h

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ValueCoproducts
