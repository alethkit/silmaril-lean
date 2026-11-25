module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.Packing.Defs
public import Silmaril.SSA.Thesis.SyntacticCategory.Packing.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Syntactic.Packing

/-! # Packed native LetIter reification -/

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

open CategoryTheory
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation Tm)
open Silmaril.Thesis.LambdaIter.LocallyNameless (HasType)
open Silmaril.Thesis.LambdaIter.Syn.SynCat

local notation "bindArrow" => ProofRelevant.Semantics.Categorical.bind

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]

/-- Packing the native denotation of an application leaves the instruction as postcomposition. -/
theorem packedNative_op (pe : ε) {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {f : Φ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t (instrSrc f)) :
    packedNative pe (.op (f := f) d) =
      packedNative pe d ≫ (instructionModel (τ := τ) pe).denote f :=
  (Category.assoc _ _ _).symm

/-- Packing the native denotation of a let gives binding on the packed context. -/
theorem packedNative_let1 (pe : ε) {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n}
    {s : Tm Empty Φ (n + 1)} {A B : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t A)
    (e : Derivation Φ (Ctx.nil : Ctx Empty τ) (.snoc β A) s B) :
    packedNative pe (.let₁ d e) =
      bindArrow (values (signature (τ := τ) (Φ := Φ) pe)) (packedNative pe d) (packedNative pe e) :=
  PackingProofs.packedNative_let1 pe d e

local instance : Thesis.LambdaIter.TypeFormers τ := Bridge.thesisTypeFormers τ
local instance : Thesis.LambdaIter.HasTy Φ τ := Bridge.thesisHasTy Φ τ

/-- An arbitrary bound-variable lookup reifies to the packed context projection. -/
theorem packedNative_bv_eq_packedArrow (pe : ε)
    {n : Nat} {β : BoundCtx τ n} (i : Fin n)
    (h : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (Bridge.BoundCtx.toThesis β) (.bv i) (β.get i)) :
    packedNative pe (Derivation.bv (Φ := Φ) (Γ := (Ctx.nil : Ctx Empty τ)) (ι := i) (β := β)) =
      packedArrow (S := signature (τ := τ) (Φ := Φ) pe) h :=
  PackingProofs.packedNative_bv_eq_packedArrow pe i h

/-- The packed denotation of unit is the packed syntactic unit. -/
theorem packedNative_unit_eq_packedArrow (pe : ε) {n : Nat} {β : BoundCtx τ n}
    (h : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (Bridge.BoundCtx.toThesis β) .unit (Silmaril.unit : τ)) :
    packedNative pe (Derivation.unit (Φ := Φ) (Γ := (Ctx.nil : Ctx Empty τ)) (β := β)) =
      packedArrow (S := signature (τ := τ) (Φ := Φ) pe) h :=
  PackingProofs.packedNative_unit_eq_packedArrow pe h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Reification of an argument implies reification after applying a primitive. -/
theorem packedNative_op_eq_packedArrow (pe : ε)
    {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {f : Φ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t (instrSrc f))
    (h : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (Bridge.BoundCtx.toThesis β) (Bridge.toThesis t) (instrSrc f))
    (ih : packedNative pe d = packedArrow (S := signature (τ := τ) (Φ := Φ) pe) h) :
    packedNative pe (.op (f := f) d) =
      packedArrow (S := signature (τ := τ) (Φ := Φ) pe) (HasType.op (f := f) h) := by
  rw [packedNative_op pe d, ih, packedArrow_op h]
  rfl

/-- Reification of the scrutinee and body implies reification of their let. -/
theorem packedNative_let1_eq_packedArrow (pe : ε)
    {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {s : Tm Empty Φ (n + 1)} {A B : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t A)
    (e : Derivation Φ (Ctx.nil : Ctx Empty τ) (.snoc β A) s B)
    (ha : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (Bridge.BoundCtx.toThesis β) (Bridge.toThesis t) A)
    (hb : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (.snoc (Bridge.BoundCtx.toThesis β) A) (Bridge.toThesis s) B)
    (ih₁ : packedNative pe d = packedArrow (S := signature (τ := τ) (Φ := Φ) pe) ha)
    (ih₂ : packedNative pe e = packedArrow (S := signature (τ := τ) (Φ := Φ) pe) hb) :
    packedNative pe (.let₁ d e) =
      packedArrow (S := signature (τ := τ) (Φ := Φ) pe) (.let₁ ha hb) :=
  PackingProofs.packedNative_let1_eq_packedArrow pe d e ha hb ih₁ ih₂

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
