module

public import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.TypeChangeLetCase

public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory
open Morphism (SignatureMap)
open Theory (TypingIndex)
open Isotope.LetCase.LocallyNameless
open Silmaril.Logic.Metatheory.TheoryModel

variable {τ υ κ ε δ ξ : Type} [TypeFormers τ] [TypeFormers υ] [TypeFormers κ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ} {S : InstrSig κ ξ}
  (g : SignatureMap P.Instr Q.Instr τ υ ε δ)
  (h : SignatureMap Q.Instr S.Instr υ κ δ ξ)
  [g.PreservesProducts] [g.PreservesSums] [h.PreservesProducts] [h.PreservesSums]

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)
local notation "Δ₀" => (Ctx.nil : Ctx Empty υ)
local notation "S₀" => Models.signature P.Instr Γ₀
local notation "T₀" => Models.signature Q.Instr Δ₀

private theorem castCarrier_fst {i j : TypingIndex υ} (e : i = j)
    (a : Models.Carrier Q.Instr Δ₀ i) :
    HEq (@Eq.rec _ _ (fun i _ => Models.Carrier Q.Instr Δ₀ i) a _ e).1 a.1 := by
  subst j
  rfl

private theorem castCarrier_snd {i j : TypingIndex υ} (e : i = j)
    (a : Models.Carrier Q.Instr Δ₀ i) :
    HEq (@Eq.rec _ _ (fun i _ => Models.Carrier Q.Instr Δ₀ i) a _ e).2 a.2 := by
  subst j
  rfl

private theorem mappedSyntaxArgs_fst {i : TypingIndex τ} (o : (S₀).Op i)
    (a : ∀ j, Models.Carrier Q.Instr Δ₀ (mapTypingIndex g ((S₀).argSort o j)))
    (j : Fin ((T₀).arity (mappedCaseOp g o).2)) (k : Fin ((S₀).arity o))
    (e : j.val = k.val) :
    HEq (mappedCaseArgs g (Models.syntaxAlgebra Q.Instr Δ₀) o a j).1 (a k).1 := by
  have same : Fin.cast (mappedCaseOp_arity g o) j = k := Fin.ext e
  subst k
  exact castCarrier_fst (Q := Q) (mappedCaseOp_args g o j) _

private theorem mappedSyntaxArgs_snd {i : TypingIndex τ} (o : (S₀).Op i)
    (a : ∀ j, Models.Carrier Q.Instr Δ₀ (mapTypingIndex g ((S₀).argSort o j)))
    (j : Fin ((T₀).arity (mappedCaseOp g o).2)) (k : Fin ((S₀).arity o))
    (e : j.val = k.val) :
    HEq (mappedCaseArgs g (Models.syntaxAlgebra Q.Instr Δ₀) o a j).2 (a k).2 := by
  have same : Fin.cast (mappedCaseOp_arity g o) j = k := Fin.ext e
  subst k
  exact castCarrier_snd (Q := Q) (mappedCaseOp_args g o j) _

local macro "stripResultCasts" : tactic => `(tactic|
  iterate 3
    try first
      | refine (eqRec_heq _ _).trans ?_
      | refine HEq.trans ?_ (eqRec_heq _ _).symm
)

-- Nullary constructors close by reflexivity before the argument transport steps.
set_option linter.unusedTactic false in
set_option backward.isDefEq.respectTransparency false in
private theorem syntaxMap_comm {i : TypingIndex τ} (o : (S₀).Op i)
    (a : (j : Fin ((S₀).arity o)) → Models.Carrier P.Instr Γ₀ ((S₀).argSort o j)) :
    (LambdaSSA.Acyclic.Operand.mapSignature g (Models.syntaxOp o a) :
      Models.Carrier Q.Instr Δ₀ (mapTypingIndex g i)) =
      (Algebra.reductObj (typeCaseSignatureHom g) (Models.syntaxAlgebra Q.Instr Δ₀)).op o
        (fun j => LambdaSSA.Acyclic.Operand.mapSignature g (a j)) := by
  apply eq_of_heq
  refine HEq.trans ?_ (typeCaseHom_reductOp_heq g (Models.syntaxAlgebra Q.Instr Δ₀) o
    (fun j => LambdaSSA.Acyclic.Operand.mapSignature g (a j))).symm
  have haF j k e := mappedSyntaxArgs_fst g o
    (fun i => LambdaSSA.Acyclic.Operand.mapSignature g (a i)) j k e
  have haD j k e := mappedSyntaxArgs_snd g o
    (fun i => LambdaSSA.Acyclic.Operand.mapSignature g (a i)) j k e
  cases o with
  | @fv n β x A hx => exact x.elim
  | _ =>
    first
    | rfl
    | simp only [Models.syntaxAlgebra, Models.syntaxOp, mappedCaseOp,
        LambdaSSA.Acyclic.Operand.mapSignature, Derivation.mapSignature, Tm.mapInstr]
      congr! (config := .unfoldSameFun) 1
      all_goals
        stripResultCasts
        first | rfl | solve
          | funext t; congr 1; simp [g.target]
          | congr! (config := .unfoldSameFun) 1 <;> stripResultCasts <;>
              first
              | rfl
              | exact eq_of_heq (haF (0 : Fin 1) (0 : Fin 1) rfl).symm
              | exact eq_of_heq (haF (0 : Fin 2) (0 : Fin 2) rfl).symm
              | exact eq_of_heq (haF (0 : Fin 3) (0 : Fin 3) rfl).symm
              | exact (haD (0 : Fin 1) (0 : Fin 1) rfl).symm
              | exact (haD (0 : Fin 2) (0 : Fin 2) rfl).symm
              | exact (haD (0 : Fin 3) (0 : Fin 3) rfl).symm

/-- The typed derivation map is the fold into the reduct of target syntax. -/
def typeCaseSyntaxMap (g : SignatureMap P.Instr Q.Instr τ υ ε δ)
    [g.PreservesProducts] [g.PreservesSums] :
    Models.syntaxAlgebra P.Instr Γ₀ ⟶
      Algebra.reductObj (typeCaseSignatureHom g) (Models.syntaxAlgebra Q.Instr Δ₀) where
  map a := LambdaSSA.Acyclic.Operand.mapSignature g a
  comm := syntaxMap_comm g

theorem typeCaseHom_translate_proof (e : CaseEquation P) :
    PresSig.mapEquation (X := LetCase.presObj Γ₀ P) (Y := LetCase.presObj Δ₀ Q)
      (typeCaseSignatureHom g) e = mapCaseSignature g e := by
  have ht : PresSig.translate (X := LetCase.presObj Γ₀ P) (Y := LetCase.presObj Δ₀ Q)
      (typeCaseSignatureHom g) = typeCaseSyntaxMap g :=
    (LetCase.presObj Γ₀ P).isInitial.hom_ext _ _
  unfold PresSig.mapEquation
  rw [ht]
  rfl

private theorem caseEquation_left_heq {e e' : CaseEquation Q} (h : e = e') :
    HEq e.2.1 e'.2.1 := by
  cases h
  rfl

private theorem mapOperand_primitive_heq {P Q : InstrSig τ ε} (f : P ⟶ Q)
    {n : Nat} {β : BoundCtx τ n} {A : τ} (a : LambdaSSA.Acyclic.Operand P.Instr β A) :
    HEq (a.mapSignature f.toSignatureMap) (mapOperand f a) := by
  have e := typeCaseHom_translate_proof f.toSignatureMap (⟨⟨n, β, A⟩, a, a⟩ : CaseEquation P)
  rw [typeCaseHom_primitive_proof] at e
  exact (caseEquation_left_heq e).symm

private theorem codeSignature_primitive_heq {P Q : InstrSig τ ε} (f : P ⟶ Q)
    {n : Nat} {β : BoundCtx τ n} {A : τ} (c : LambdaSSA.Acyclic.Code P.Instr β A) :
    HEq (c.mapSignature f.toSignatureMap) (mapCode f c) := by
  induction c with
  | br a =>
    have ea := mapOperand_primitive_heq f a
    simp only [LambdaSSA.Acyclic.Code.mapSignature, mapCode]
    congr! (config := .unfoldSameFun) 1
    simp [InstrSig.Hom.toSignatureMap]
  | let₁ a _ ih =>
    have ea := mapOperand_primitive_heq f a
    simp only [LambdaSSA.Acyclic.Code.mapSignature, mapCode]
    congr! (config := .unfoldSameFun) 1
    simp [InstrSig.Hom.toSignatureMap]
  | let₂ a _ ih =>
    have ea := mapOperand_primitive_heq f a
    simp only [LambdaSSA.Acyclic.Code.mapSignature, mapCode]
    congr! (config := .unfoldSameFun) 1
    simp [InstrSig.Hom.toSignatureMap]
  | case a _ _ ihl ihr =>
    have ea := mapOperand_primitive_heq f a
    simp only [LambdaSSA.Acyclic.Code.mapSignature, mapCode]
    congr! (config := .unfoldSameFun) 1
    simp [InstrSig.Hom.toSignatureMap]
  | join a b iha ihb =>
    simp only [LambdaSSA.Acyclic.Code.mapSignature, mapCode]
    congr! (config := .unfoldSameFun) 1
    simp [InstrSig.Hom.toSignatureMap]

theorem mapSSASignature_primitive_proof {P Q : InstrSig τ ε} (f : P ⟶ Q) (e : SSAEquation P) :
    mapSSASignature f.toSignatureMap e = mapEquation f e := by
  obtain ⟨⟨n, β, A⟩, l, r⟩ := e
  have hl := codeSignature_primitive_heq f l
  have hr := codeSignature_primitive_heq f r
  unfold mapSSASignature mapEquation mapTypingIndex
  congr! (config := .unfoldSameFun) 2 <;> simp [InstrSig.Hom.toSignatureMap]

end Silmaril.Isotope.Institution.Acyclic
