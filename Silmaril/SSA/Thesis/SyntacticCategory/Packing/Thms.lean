module

public import Silmaril.SSA.Thesis.SyntacticCategory.Packing.Defs
public import Silmaril.SSA.Thesis.SyntacticCategory.Tensor.Structure.Defs
import Silmaril.Proofs.SSA.Thesis.SyntacticCategory.Packing.Reflection

/-! # Context packing and reflection in the one-variable λiter syntactic category -/

public section

universe u

namespace Silmaril.Thesis.LambdaIter.Syn.SynCat

open CategoryTheory
open LocallyNameless
open Silmaril.Thesis.LambdaIter (instrSrc instrTrg)

variable {S : Sig.{u}}

/-- Opening a packed term with the tuple of the original context recovers the term
up to exact λiter equality. -/
theorem unpacked_packed {n : Nat} {β : BoundCtx S.Ty n}
    {t : Tm Empty S.Instr n} {A : S.Ty} (h : HasType S.Instr Ctx.nil β t A) :
    Eqv S.pureEff Ctx.nil β (unpackedTerm β (packedTerm β t)) t A :=
  unpacked_packed_proof h

/-- Packing a one-variable term opened with the tuple recovers the one-variable term. -/
theorem packed_unpacked {n : Nat} (β : BoundCtx S.Ty n)
    {t : Tm Empty S.Instr 1} {A : S.Ty}
    (h : HasType S.Instr Ctx.nil (.snoc .nil (packType β)) t A) :
    Eqv S.pureEff Ctx.nil (.snoc .nil (packType β))
      (packedTerm β (unpackedTerm β t)) t A :=
  packed_unpacked_proof β h

/-- The typed quotient in an arbitrary bound context is equivalent to the hom
from its packed product object. The inverse substitutes the tuple. -/
def packedHomEquiv {n : Nat} (β : BoundCtx S.Ty n) (A : S.Ty) :
    El S β A ≃ (of (packType β) ⟶ of A) :=
  packedHomEquiv_proof β A

/-- On representatives the equivalence computes the packed arrow. -/
@[simp] theorem packedHomEquiv_mk {n : Nat} {β : BoundCtx S.Ty n}
    {t : Tm Empty S.Instr n} {A : S.Ty} (h : HasType S.Instr Ctx.nil β t A) :
    packedHomEquiv β A (mk h) = packedArrow h := packedHomEquiv_mk_proof h

/-- With empty free context, equality of the packed syntactic arrows is equivalent to
exact λiter equality in the original bound context. -/
theorem packedArrow_eq_iff {n : Nat} {β : BoundCtx S.Ty n} {A : S.Ty}
    {t v : Tm Empty S.Instr n}
    (h : HasType S.Instr Ctx.nil β t A) (k : HasType S.Instr Ctx.nil β v A) :
    packedArrow h = packedArrow k ↔ Eqv S.pureEff Ctx.nil β t v A := by
  rw [← packedHomEquiv_mk h, ← packedHomEquiv_mk k, (packedHomEquiv β A).injective.eq_iff]
  exact ⟨Syn.eqv_of_mk_eq, Syn.mk_eq_mk h k⟩

/-- The newest packed bound variable is the second projection. -/
theorem packedArrow_bv_zero {n : Nat} (β : BoundCtx S.Ty n) (A : S.Ty) :
    packedArrow (S := S) (HasType.bv (β := .snoc β A) (ι := 0)) =
      second (of (packType β)) (of A) := rfl

/-- An older packed bound variable is obtained by first dropping the newest one. -/
theorem packedArrow_bv_succ {n : Nat} (β : BoundCtx S.Ty n) (A : S.Ty) (i : Fin n) :
    packedArrow (S := S) (HasType.bv (β := .snoc β A) (ι := i.succ)) =
      first (of (packType β)) (of A) ≫ packedArrow (HasType.bv (β := β) (ι := i)) :=
  packedArrow_bv_succ_proof β A i

/-- A packed instruction is composition with the instruction on its input variable. -/
theorem packedArrow_op {n : Nat} {β : BoundCtx S.Ty n} {a : Tm Empty S.Instr n}
    {f : S.Instr} (ha : HasType S.Instr Ctx.nil β a (instrSrc f)) :
    packedArrow (S := S) (HasType.op (f := f) ha) =
      packedArrow ha ≫ mk (S := S) (HasType.op (f := f) HasType.newest) :=
  packedArrow_op_proof ha

/-- Packing a let retains the packed context while evaluating the scrutinee,
then composes with the packed body. -/
theorem packedArrow_let1 {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty}
    {a : Tm Empty S.Instr n} {b : Tm Empty S.Instr (n + 1)}
    (ha : HasType S.Instr Ctx.nil β a A) (hb : HasType S.Instr Ctx.nil (.snoc β A) b B) :
    packedArrow (S := S) (.let₁ ha hb) =
      pairArrows (𝟙 (of (packType β))) (packedArrow ha) ≫ packedArrow hb :=
  packedArrow_let1_proof ha hb

/-- A packed left injection is postcomposition with the syntactic injection. -/
theorem packedArrow_inl {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty}
    {a : Tm Empty S.Instr n} (h : HasType S.Instr Ctx.nil β a A) :
    packedArrow (S := S) (HasType.inl (B := B) h) =
      packedArrow h ≫ injl (of A) (of B) :=
  packedArrow_inl_proof h

/-- A packed right injection is postcomposition with the syntactic injection. -/
theorem packedArrow_inr {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty}
    {a : Tm Empty S.Instr n} (h : HasType S.Instr Ctx.nil β a B) :
    packedArrow (S := S) (HasType.inr (A := A) h) =
      packedArrow h ≫ injr (of A) (of B) :=
  packedArrow_inr_proof h

/-- Packing a product elimination retains the input and reassociates the two bound slots. -/
theorem packedArrow_let2 {n : Nat} {β : BoundCtx S.Ty n} {A B C : S.Ty}
    {a : Tm Empty S.Instr n} {c : Tm Empty S.Instr (n + 2)}
    (ha : HasType S.Instr Ctx.nil β a (tensor A B))
    (hc : HasType S.Instr Ctx.nil ((β.snoc A).snoc B) c C) :
    packedArrow (S := S) (.let₂ ha hc) =
      pairArrows (𝟙 (of (packType β))) (packedArrow ha) ≫
        (tensorAssociator (of (packType β)) (of A) (of B)).inv ≫ packedArrow hc :=
  packedArrow_let2_proof ha hc

/-- Packing a pair substitutes the packed projections in each component. -/
theorem packedArrow_pair {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty}
    {a b : Tm Empty S.Instr n} (ha : HasType S.Instr Ctx.nil β a A)
    (hb : HasType S.Instr Ctx.nil β b B) :
    packedArrow (S := S) (.pair ha hb) = pairArrows (packedArrow ha) (packedArrow hb) :=
  rfl

/-- Substituting pure terms in a typed term is precomposition by their
packed context arrow. -/
theorem packedSubst_comp {n m : Nat} {β : BoundCtx S.Ty n} {γ : BoundCtx S.Ty m}
    {σ : Fin n → Tm Empty S.Instr m}
    (s : PureTypedSubst (Γ := Ctx.nil) (pureEff := S.pureEff) β γ σ)
    {t : Tm Empty S.Instr n} {A : S.Ty} (h : HasType S.Instr Ctx.nil β t A) :
    packedSubst s ≫ packedArrow h = packedArrow (h.bsubst s.typed) :=
  packedSubst_comp_proof s h

/-- The packed context arrow of a pure substitution is a syntactic value arrow. -/
theorem packedSubst_isPureMor {n m : Nat} {β : BoundCtx S.Ty n} {γ : BoundCtx S.Ty m}
    {σ : Fin n → Tm Empty S.Instr m}
    (s : PureTypedSubst (Γ := Ctx.nil) (pureEff := S.pureEff) β γ σ) :
    IsPureMor (packedSubst s) :=
  packedSubst_isPureMor_proof s

/-- The pure substitution used by packing preserves syntactic purity. -/
theorem packedTerm_pure {n : Nat} (β : BoundCtx S.Ty n) {t : Tm Empty S.Instr n}
    (hp : Pure S.pureEff t) : Pure S.pureEff (packedTerm β t) :=
  packedTerm_pure_proof β hp

/-- Packing a pure term uses pure projections and preserves purity. -/
theorem packedArrow_isPureMor {n : Nat} {β : BoundCtx S.Ty n} {A : S.Ty}
    {t : Tm Empty S.Instr n} (h : HasType S.Instr Ctx.nil β t A) (hp : Pure S.pureEff t) :
    IsPureMor (packedArrow h) :=
  packedArrow_isPureMor_proof h hp

end Silmaril.Thesis.LambdaIter.Syn.SynCat
