module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.FiniteExit.Signature.Defs

public section

set_option backward.isDefEq.respectTransparency false

namespace Silmaril.Isotope.LambdaSSA.Acyclic.FiniteExit

open Morphism (SignatureMap)
open Institution (InstrSig)
open Institution.Acyclic
open Morphism.CaseSSA (erase_mapInstr)
open Region (packedExitType)
open LetCase.LocallyNameless (Derivation Tm)

variable {τ υ ε δ : Type} [TypeFormers τ] [TypeFormers υ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ}
  (g : SignatureMap P.Instr Q.Instr τ υ ε δ) [g.PreservesProducts] [g.PreservesSums]
  {L : LCtx τ} {n : Nat} {β : BoundCtx τ n}

omit [g.PreservesProducts] in
theorem packedExitType_map_proof (L : LCtx τ) :
    g.ty (packedExitType L) = packedExitType (L.map g.ty) := by
  induction L with
  | nil => exact SignatureMap.PreservesSums.empty (g := g)
  | cons A L ih => simp only [packedExitType, List.map_cons, SignatureMap.PreservesSums.coprod, ih]

theorem toSSA_mapSignature_proof (c : FiniteExit P.Instr L β) :
    (c.mapSignature g).toSSA = c.toSSA.mapInstr g.instr := by
  induction c with
  | br hi a => simp [mapSignature, toSSA, Operand.mapSignature, Region.mapInstr, erase_mapInstr]
  | case e l r hl hr =>
    simp [mapSignature, toSSA, Operand.mapSignature, Operand.castResult, Region.mapInstr, erase_mapInstr, hl, hr]
  | join a b hb =>
    simp [mapSignature, toSSA, Region.linkExits, Region.mapInstr, Region.mapInstr_renameLabels,
      Code.toSSA_mapSignature, hb]

private theorem castOperand_heq {X Y : υ} {γ : BoundCtx υ n} (e : X = Y)
    (a : Operand Q.Instr γ X) : HEq (a.castResult e) a := by
  cases e
  rfl

private theorem map_inl_heq {X Y : τ} (a : Operand P.Instr β X) :
    HEq (Operand.mapSignature g (⟨.inl a.1, .inl a.2⟩ : Operand P.Instr β (coprod X Y)))
      (⟨.inl (a.mapSignature g).1, .inl (a.mapSignature g).2⟩ :
        Operand Q.Instr (β.mapTypes g.ty) (coprod (g.ty X) (g.ty Y))) := by
  let b : Operand Q.Instr (β.mapTypes g.ty) (coprod (g.ty X) (g.ty Y)) :=
    ⟨.inl (a.mapSignature g).1, .inl (a.mapSignature g).2⟩
  change HEq (b.castResult (SignatureMap.PreservesSums.coprod (g := g) X Y).symm) b
  exact castOperand_heq _ b

private theorem map_inr_heq {X Y : τ} (a : Operand P.Instr β Y) :
    HEq (Operand.mapSignature g (⟨.inr a.1, .inr a.2⟩ : Operand P.Instr β (coprod X Y)))
      (⟨.inr (a.mapSignature g).1, .inr (a.mapSignature g).2⟩ :
        Operand Q.Instr (β.mapTypes g.ty) (coprod (g.ty X) (g.ty Y))) := by
  let b : Operand Q.Instr (β.mapTypes g.ty) (coprod (g.ty X) (g.ty Y)) :=
    ⟨.inr (a.mapSignature g).1, .inr (a.mapSignature g).2⟩
  change HEq (b.castResult (SignatureMap.PreservesSums.coprod (g := g) X Y).symm) b
  exact castOperand_heq _ b

private theorem inr_operand_heq {X Y Z : υ} {γ : BoundCtx υ n}
    {a : Operand Q.Instr γ Y} {b : Operand Q.Instr γ Z} (e : Y = Z) (hab : HEq a b) :
    HEq (⟨.inr a.1, .inr a.2⟩ : Operand Q.Instr γ (coprod X Y))
      (⟨.inr b.1, .inr b.2⟩ : Operand Q.Instr γ (coprod X Z)) := by
  cases e
  cases eq_of_heq hab
  rfl

private theorem inl_other_heq {X Y Z : υ} {γ : BoundCtx υ n}
    (a : Operand Q.Instr γ X) (e : Y = Z) :
    HEq (⟨.inl a.1, .inl a.2⟩ : Operand Q.Instr γ (coprod X Y))
      (⟨.inl a.1, .inl a.2⟩ : Operand Q.Instr γ (coprod X Z)) := by
  cases e
  rfl

private theorem tag_map_heq (L : LCtx τ) (i : Nat) {A : τ} (hi : At L i A)
    (a : Operand P.Instr β A) :
    HEq ((tag L i hi a).mapSignature g)
      (tag (L.map g.ty) i (mapContextLookup g.ty hi) (a.mapSignature g)) := by
  induction L generalizing i with
  | nil => simp [At] at hi
  | cons B L ih =>
    cases i with
    | zero =>
      cases Option.some.inj hi
      change HEq ((tag (A :: L) 0 rfl a).mapSignature g)
        (tag (g.ty A :: L.map g.ty) 0 rfl (a.mapSignature g))
      simpa only [tag, eqRec_eq_cast] using
        (map_inl_heq g (Y := packedExitType L) a).trans
          (inl_other_heq (a.mapSignature g) (packedExitType_map_proof g L))
    | succ i =>
      have hi' : At L i A := hi
      exact (map_inr_heq g (X := B) (tag L i hi' a)).trans
        (inr_operand_heq (X := g.ty B) (packedExitType_map_proof g L) (ih i hi'))

theorem encode_mapSignature_heq_proof (c : FiniteExit P.Instr L β) :
    HEq (c.encode.mapSignature g) (c.mapSignature g).encode := by
  induction c with
  | br hi a =>
    have ht := tag_map_heq g L _ hi a
    simp only [encode, mapSignature, Code.mapSignature]
    congr! (config := .unfoldSameFun) 1
    exact packedExitType_map_proof g L
  | case e l r hl hr =>
    simp only [encode, mapSignature, Code.mapSignature]
    congr! (config := .unfoldSameFun) 1
    exact packedExitType_map_proof g L
  | join a b hb =>
    simp only [encode, mapSignature, Code.mapSignature]
    congr! (config := .unfoldSameFun) 1
    exact packedExitType_map_proof g L

theorem mapSignature_id_heq_proof (c : FiniteExit P.Instr L β) :
    HEq (c.mapSignature (SignatureMap.id (Φ := P.Instr) (τ := τ) (ε := ε))) c := by
  induction c with
  | br hi a =>
    have ea := operandSignature_id_heq a
    simp only [mapSignature]
    congr! (config := .unfoldSameFun) 1 <;> simp [SignatureMap.id]
  | case a _ _ ihl ihr =>
    have ea := operandSignature_id_heq a
    simp only [mapSignature]
    congr! (config := .unfoldSameFun) 1 <;> simp [SignatureMap.id]
  | join a _ ih =>
    have ea := singleCodeSignature_id_heq a
    simp only [mapSignature]
    congr! (config := .unfoldSameFun) 1 <;> simp [SignatureMap.id]

variable {κ ξ : Type} [TypeFormers κ] {S : InstrSig κ ξ}
  (h : SignatureMap Q.Instr S.Instr υ κ δ ξ) [h.PreservesProducts] [h.PreservesSums]

theorem mapSignature_comp_heq_proof (c : FiniteExit P.Instr L β) :
    HEq (c.mapSignature (h.comp g)) ((c.mapSignature g).mapSignature h) := by
  induction c with
  | br hi a =>
    have ea := operandSignature_comp_heq g h a
    simp only [mapSignature]
    congr! (config := .unfoldSameFun) 1 <;> simp [SignatureMap.comp]
  | @case n β A B a _ _ ihl ihr =>
    have ea := operandSignature_comp_cast_heq g h a
      (SignatureMap.PreservesSums.coprod (g := g) A B)
      (SignatureMap.PreservesSums.coprod (g := h) (g.ty A) (g.ty B))
      (SignatureMap.PreservesSums.coprod (g := h.comp g) A B)
    simp only [mapSignature]
    congr! (config := .unfoldSameFun) 1 <;> simp [SignatureMap.comp]
  | join a _ ih =>
    have ea := singleCodeSignature_comp_heq g h a
    simp only [mapSignature]
    congr! (config := .unfoldSameFun) 1 <;> simp [SignatureMap.comp]

end Silmaril.Isotope.LambdaSSA.Acyclic.FiniteExit
