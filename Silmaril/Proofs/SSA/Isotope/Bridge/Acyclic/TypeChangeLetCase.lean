module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.TypeChange.LetCase.Signature.Defs
public import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.TypeChangeCaseOperation

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

private theorem typeCaseHom_argVal : SigHomArgVal (typeCaseSignatureHom g) :=
  fun _ _ => rfl

private theorem typeCaseHom_op_heq {i : TypingIndex τ} (o : (S₀).Op i) :
    HEq ((typeCaseSignatureHom g).op o) (mappedCaseOp g o).2 :=
  castOp_heq (S := T₀) (mappedCaseOp_index g o) (mappedCaseOp g o).2

theorem typeCaseHom_id_proof :
    typeCaseSignatureHom (P := P) (Q := P) SignatureMap.id = Signature.Hom.id S₀ := by
  refine sigHom_ext_of_argVal (funext fun i => ?_) (fun o => ?_)
    (typeCaseHom_argVal SignatureMap.id) (sigHomArgVal_id _)
  · cases i
    simp [typeCaseSignatureHom, Signature.Hom.id, mapTypingIndex, SignatureMap.id]
  · refine (typeCaseHom_op_heq (P := P) (Q := P) SignatureMap.id o).trans ?_
    cases o with
    | @fv n β x A hx => exact x.elim
    | _ =>
      simp only [mappedCaseOp, Signature.Hom.id]
      congr! (config := .unfoldSameFun) 1
      simp [SignatureMap.id]

theorem typeCaseHom_comp_proof :
    typeCaseSignatureHom (h.comp g) = (typeCaseSignatureHom h).comp (typeCaseSignatureHom g) := by
  refine sigHom_ext_of_argVal (funext fun i => ?_) (fun o => ?_)
    (typeCaseHom_argVal (h.comp g)) (sigHomArgVal_comp (typeCaseHom_argVal h) (typeCaseHom_argVal g))
  · cases i
    simp [typeCaseSignatureHom, Signature.Hom.comp, mapTypingIndex, SignatureMap.comp]
  · refine (typeCaseHom_op_heq (h.comp g) o).trans
      (HEq.trans (b := (mappedCaseOp h (mappedCaseOp g o).2).2) ?_ ?_)
    · show HEq (mappedCaseOp (h.comp g) o).2 (mappedCaseOp h (mappedCaseOp g o).2).2
      cases o with
      | @fv n β x A hx => exact x.elim
      | _ =>
        simp only [mappedCaseOp]
        congr! (config := .unfoldSameFun) 1
        simp [SignatureMap.comp]
    · exact (typeCaseHom_op_heq h (mappedCaseOp g o).2).symm.trans
        (heq_apply_castOp (fun _ o => (typeCaseSignatureHom h).op o) (mappedCaseOp_index g o)
          (mappedCaseOp g o).2).symm

theorem typeCaseHom_primitive_proof {P Q : InstrSig τ ε} (f : P ⟶ Q) :
    typeCaseSignatureHom f.toSignatureMap = LetCase.sigHom Γ₀ f := by
  refine sigHom_ext_of_argVal (funext fun i => ?_) (fun o => ?_)
    (typeCaseHom_argVal f.toSignatureMap) (LetCase.sigHom_argVal Γ₀ f)
  · cases i
    simp [typeCaseSignatureHom, LetCase.sigHom, mapTypingIndex, InstrSig.Hom.toSignatureMap]
  · refine (typeCaseHom_op_heq f.toSignatureMap o).trans ?_
    cases o with
    | @fv n β x A hx => exact x.elim
    | @op n β x =>
      change HEq _ (LetCase.opMap Γ₀ f (.op (β := β) x))
      refine HEq.trans ?_ (LetCase.opMap_op_heq Γ₀ f (β := β) x).symm
      simp only [mappedCaseOp]
      congr! (config := .unfoldSameFun) 1
      simp [InstrSig.Hom.toSignatureMap]
    | _ =>
      simp only [mappedCaseOp, LetCase.sigHom, LetCase.opMap]
      congr! (config := .unfoldSameFun) 1
      simp [InstrSig.Hom.toSignatureMap]

/-- Target arguments before the transport of the operation's result sort. -/
@[expose] def mappedCaseArgs (M : Algebra.{0, 0, 0} T₀) {i : TypingIndex τ} (o : (S₀).Op i)
    (a : (j : Fin ((S₀).arity o)) → M.Carrier (mapTypingIndex g ((S₀).argSort o j)))
    (j : Fin ((T₀).arity (mappedCaseOp g o).2)) :
    M.Carrier ((T₀).argSort (mappedCaseOp g o).2 j) :=
  mappedCaseOp_args g o j ▸ a (Fin.cast (mappedCaseOp_arity g o) j)

private theorem castOp_apply_heq {I : Type} {T : Silmaril.Logic.Metatheory.TheoryModel.Signature.{0, 0} I}
    (M : Algebra.{0, 0, 0} T) {i j : I} (e : i = j) (o : T.Op i)
    (a : (k : Fin (T.arity (castOp T e o))) → M.Carrier (T.argSort (castOp T e o) k))
    (b : (k : Fin (T.arity o)) → M.Carrier (T.argSort o k))
    (h : ∀ k, HEq (a k) (b (Fin.cast (arity_castOp T e o) k))) :
    HEq (M.op (castOp T e o) a) (M.op o b) := by
  subst j
  apply heq_of_eq
  congr 1
  funext k
  exact eq_of_heq (h k)

theorem typeCaseHom_reductOp_heq (M : Algebra.{0, 0, 0} T₀) {i : TypingIndex τ}
    (o : (S₀).Op i) (a : (j : Fin ((S₀).arity o)) → M.Carrier (mapTypingIndex g ((S₀).argSort o j))) :
    HEq ((Algebra.reductObj (typeCaseSignatureHom g) M).op o a)
      (M.op (mappedCaseOp g o).2 (mappedCaseArgs g M o a)) := by
  apply castOp_apply_heq M (mappedCaseOp_index g o)
  intro k
  exact (eqRec_heq _ _).trans (eqRec_heq _ _).symm

end Silmaril.Isotope.Institution.Acyclic
