module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.TypeChange.Defs

public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory
open Morphism (SignatureMap)
open LambdaSSA.Acyclic (Code Operand)
open LetCase.LocallyNameless (Tm Derivation)

variable {τ υ κ ε δ ξ : Type} [TypeFormers τ] [TypeFormers υ] [TypeFormers κ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ} {S : InstrSig κ ξ}
  (g : SignatureMap P.Instr Q.Instr τ υ ε δ)
  (h : SignatureMap Q.Instr S.Instr υ κ δ ξ)
  [g.PreservesProducts] [g.PreservesSums] [h.PreservesProducts] [h.PreservesSums]
  {n : Nat} {β : BoundCtx τ n} {A : τ}

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)

private theorem mapDerivation_result_cast_heq {Γ : Ctx Empty υ} {n : Nat} {γ : BoundCtx υ n}
    {t : Tm Empty Q.Instr n} {A B : υ} (e : A = B)
    (d : Derivation Q.Instr Γ γ t A) :
    HEq ((@Eq.rec υ A (fun X _ => Derivation Q.Instr Γ γ t X) d B e).mapSignature h)
      (d.mapSignature h) := by
  subst B
  rfl

local macro "stripDerivationCasts" : tactic => `(tactic|
  iterate 4
    try first
      | refine (eqRec_heq _ _).trans ?_
      | refine HEq.trans ?_ (eqRec_heq _ _).symm
      | refine HEq.trans ?_ (mapDerivation_result_cast_heq _ _ _).symm
)

private theorem mapDerivation_id {t : Tm Empty P.Instr n} (d : Derivation P.Instr Γ₀ β t A) :
    HEq (d.mapSignature (SignatureMap.id (Φ := P.Instr) (τ := τ) (ε := ε))) d := by
  induction d <;>
    simp only [Derivation.mapSignature, SignatureMap.id, id_eq] <;>
    congr! (config := .unfoldSameFun) 1 <;>
    simp
  case bv =>
    refine (eqRec_heq _ _).trans ?_
    congr! (config := .unfoldSameFun) 1
    simp

-- Some derivation constructors introduce casts and some do not.
set_option linter.unusedTactic false in
private theorem mapDerivation_comp {t : Tm Empty P.Instr n} (d : Derivation P.Instr Γ₀ β t A) :
    HEq (d.mapSignature (h.comp g)) ((d.mapSignature g).mapSignature h) := by
  induction d <;>
    simp only [Derivation.mapSignature] <;>
    stripDerivationCasts
  all_goals
    try simp only [Derivation.mapSignature]
    stripDerivationCasts
    congr! (config := .unfoldSameFun) 1
    all_goals stripDerivationCasts
    all_goals first | assumption | simp [SignatureMap.comp]

theorem mapOperand_id (a : Operand P.Instr β A) :
    HEq (a.mapSignature (SignatureMap.id (Φ := P.Instr) (τ := τ) (ε := ε))) a := by
  obtain ⟨t, d⟩ := a
  have hd := mapDerivation_id d
  unfold Operand.mapSignature
  congr! (config := .unfoldSameFun) 1 <;> simp [SignatureMap.id]

theorem mapOperand_comp (a : Operand P.Instr β A) :
    HEq (a.mapSignature (h.comp g)) ((a.mapSignature g).mapSignature h) := by
  obtain ⟨t, d⟩ := a
  have hd := mapDerivation_comp g h d
  unfold Operand.mapSignature
  congr! (config := .unfoldSameFun) 1 <;> simp [SignatureMap.comp]

private theorem castOperand_heq {σ Ψ : Type} [TypeFormers σ] [HasTy Ψ σ]
    {n : Nat} {γ : BoundCtx σ n} {A B : σ}
    (e : A = B) (a : Operand Ψ γ A) : HEq (a.castResult e) a := by
  subst B
  rfl

private theorem mapOperand_cast_heq {n : Nat} {γ : BoundCtx υ n} {A B : υ}
    (e : A = B) (a : Operand Q.Instr γ A) :
    HEq ((a.castResult e).mapSignature h) (a.mapSignature h) := by
  subst B
  rfl

theorem mapOperand_comp_cast (a : Operand P.Instr β A) {B : υ} {D : κ}
    (eg : g.ty A = B) (eh : h.ty B = D) (ec : (h.comp g).ty A = D) :
    HEq ((a.mapSignature (h.comp g)).castResult ec)
      ((((a.mapSignature g).castResult eg).mapSignature h).castResult eh) :=
  (castOperand_heq ec _).trans ((mapOperand_comp g h a).trans
    ((castOperand_heq eh _).trans (mapOperand_cast_heq h eg _)).symm)

theorem codeSignature_id_heq (c : Code P.Instr β A) :
    HEq (c.mapSignature (SignatureMap.id (Φ := P.Instr) (τ := τ) (ε := ε))) c := by
  induction c with
  | br a =>
    have ea := mapOperand_id a
    simp only [Code.mapSignature]
    congr! (config := .unfoldSameFun) 1
    simp [SignatureMap.id]
  | let₁ a _ ih =>
    have ea := mapOperand_id a
    simp only [Code.mapSignature]
    congr! (config := .unfoldSameFun) 1
    simp [SignatureMap.id]
  | let₂ a _ ih =>
    have ea := mapOperand_id a
    simp only [Code.mapSignature]
    congr! (config := .unfoldSameFun) 1
    simp [SignatureMap.id]
  | case a _ _ ihl ihr =>
    have ea := mapOperand_id a
    simp only [Code.mapSignature]
    congr! (config := .unfoldSameFun) 1
    simp [SignatureMap.id]
  | join a b iha ihb =>
    simp only [Code.mapSignature]
    congr! (config := .unfoldSameFun) 1
    simp [SignatureMap.id]

theorem codeSignature_comp_heq (c : Code P.Instr β A) :
    HEq (c.mapSignature (h.comp g)) ((c.mapSignature g).mapSignature h) := by
  induction c with
  | br a =>
    have ea := mapOperand_comp g h a
    simp only [Code.mapSignature]
    congr! (config := .unfoldSameFun) 1
    simp [SignatureMap.comp]
  | let₁ a _ ih =>
    have ea := mapOperand_comp g h a
    simp only [Code.mapSignature]
    congr! (config := .unfoldSameFun) 1
    simp [SignatureMap.comp]
  | @let₂ n β A B D a _ ih =>
    have ea := mapOperand_comp_cast g h a
      (SignatureMap.PreservesProducts.product (g := g) A B)
      (SignatureMap.PreservesProducts.product (g := h) (g.ty A) (g.ty B))
      (SignatureMap.PreservesProducts.product (g := h.comp g) A B)
    simp only [Code.mapSignature]
    congr! (config := .unfoldSameFun) 1
    simp [SignatureMap.comp]
  | @case n β A B D a _ _ ihl ihr =>
    have ea := mapOperand_comp_cast g h a
      (SignatureMap.PreservesSums.coprod (g := g) A B)
      (SignatureMap.PreservesSums.coprod (g := h) (g.ty A) (g.ty B))
      (SignatureMap.PreservesSums.coprod (g := h.comp g) A B)
    simp only [Code.mapSignature]
    congr! (config := .unfoldSameFun) 1
    simp [SignatureMap.comp]
  | join a b iha ihb =>
    simp only [Code.mapSignature]
    congr! (config := .unfoldSameFun) 1
    simp [SignatureMap.comp]

theorem mapSSASignature_id_proof (e : SSAEquation P) :
    mapSSASignature (P := P) (Q := P) SignatureMap.id e = e := by
  obtain ⟨⟨n, β, A⟩, l, r⟩ := e
  have hl := codeSignature_id_heq l
  have hr := codeSignature_id_heq r
  unfold mapSSASignature mapTypingIndex
  congr! (config := .unfoldSameFun) 2 <;> simp [SignatureMap.id]

theorem mapSSASignature_comp_proof (e : SSAEquation P) :
    mapSSASignature (h.comp g) e = mapSSASignature h (mapSSASignature g e) := by
  obtain ⟨⟨n, β, A⟩, l, r⟩ := e
  have hl := codeSignature_comp_heq g h l
  have hr := codeSignature_comp_heq g h r
  unfold mapSSASignature mapTypingIndex
  congr! (config := .unfoldSameFun) 2 <;> simp [SignatureMap.comp]

end Silmaril.Isotope.Institution.Acyclic
