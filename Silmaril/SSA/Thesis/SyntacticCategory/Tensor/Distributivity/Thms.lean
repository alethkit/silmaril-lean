module

public import Silmaril.SSA.Thesis.SyntacticCategory.Tensor.Centrality.Thms
public import Silmaril.SSA.Thesis.SyntacticCategory.Packing.Thms
import Silmaril.Proofs.SSA.Thesis.SyntacticCategory.Tensor.Distributivity

/-! # The distributive Freyd structure of exact λiter -/

public section

universe u

namespace Silmaril.Thesis.LambdaIter.Syn.SynCat

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open LocallyNameless

variable {S : Sig.{u}}

/-- A computation whose newest variable has a coproduct type can be recovered
by specializing it to the two injections and branching on that variable. -/
theorem splitSum {n : Nat} {β : BoundCtx S.Ty n} {A B D : S.Ty} {t : Tm Empty S.Instr (n + 1)}
    (h : HasType S.Instr Ctx.nil (.snoc β (coprod A B)) t D) :
    Eqv S.pureEff Ctx.nil (.snoc β (coprod A B)) t
      (.case (.bv 0)
        (Tm.bsubst (Fin.cases (.inl (.bv 0)) (fun i => .bv i.succ.succ)) t)
        (Tm.bsubst (Fin.cases (.inr (.bv 0)) (fun i => .bv i.succ.succ)) t)) D :=
  splitSum_proof h

/-- The tensored syntax injections jointly determine any computation arrow. -/
theorem tensorLeft_coprod_hom_ext (R A B : SynCat S) {D : SynCat S}
    {f g : productObj R (cop A B) ⟶ D}
    (left : tensorLeft R (injl A B) ≫ f = tensorLeft R (injl A B) ≫ g)
    (right : tensorLeft R (injr A B) ≫ f = tensorLeft R (injr A B) ≫ g) : f = g :=
  tensorLeft_coprod_hom_ext_proof R A B left right

/-- Computation tensoring distributes over binary coproducts. -/
instance computationDistributive (S : Sig.{u}) : DistributiveTensor (SynCat S) :=
  by exact computationDistributive_proof S

/-- The Cartesian value tensor distributes over binary coproducts. -/
instance valuesDistributive (S : Sig.{u}) : DistributiveTensor (ValueCat S) :=
  by exact valuesDistributive_proof S

/-- The syntactic value inclusion is distributive and preserves finite coproducts. -/
instance valuesDistributiveFreyd (S : Sig.{u}) : DistributiveFreydCategory (values S) where
  preservesFiniteCoproducts := valuesPreservesFiniteCoproducts S

/-- Distribute the retained input into the two branches of a syntactic sum. -/
noncomputable abbrev contextSumSplit (R A B : SynCat S) :
    productObj R (cop A B) ⟶ productObj R A ⨿ productObj R B :=
  tensorLeft R (copIso A B).hom ≫ DistributivePremonoidalCategory.leftInv R A B

theorem tensorLeft_injl_contextSumSplit (R A B : SynCat S) :
    tensorLeft R (injl A B) ≫ contextSumSplit R A B = coprod.inl := by
  rw [← Category.assoc, ← tensorLeft_comp, injl_copIso_hom]
  let d := DistributiveTensor.leftIso R A B
  change (R ◁ (coprod.inl : A ⟶ A ⨿ B)) ≫ d.inv = coprod.inl
  rw [← DistributiveTensor.inl_leftHom R A B, Category.assoc]
  change _ ≫ d.hom ≫ d.inv = _
  rw [d.hom_inv_id, Category.comp_id]

theorem tensorLeft_injr_contextSumSplit (R A B : SynCat S) :
    tensorLeft R (injr A B) ≫ contextSumSplit R A B = coprod.inr := by
  rw [← Category.assoc, ← tensorLeft_comp, injr_copIso_hom]
  let d := DistributiveTensor.leftIso R A B
  change (R ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫ d.inv = coprod.inr
  rw [← DistributiveTensor.inr_leftHom R A B, Category.assoc]
  change _ ≫ d.hom ≫ d.inv = _
  rw [d.hom_inv_id, Category.comp_id]

/-- A packed case retains the input, then distributes it into the selected branch. -/
theorem packedArrow_case {n : Nat} {β : BoundCtx S.Ty n} {A B D : S.Ty}
    {e : Tm Empty S.Instr n} {l r : Tm Empty S.Instr (n + 1)}
    (he : HasType S.Instr Ctx.nil β e (coprod A B))
    (hl : HasType S.Instr Ctx.nil (β.snoc A) l D) (hr : HasType S.Instr Ctx.nil (β.snoc B) r D) :
    packedArrow (S := S) (.case he hl hr) =
      pairArrows (𝟙 (of (packType β))) (packedArrow he) ≫
        contextSumSplit (of (packType β)) (of A) (of B) ≫ coprod.desc (packedArrow hl) (packedArrow hr) :=
  packedArrow_case_of_split_proof he hl hr (tensorLeft_injl_contextSumSplit _ _ _)
    (tensorLeft_injr_contextSumSplit _ _ _)

end Silmaril.Thesis.LambdaIter.Syn.SynCat
