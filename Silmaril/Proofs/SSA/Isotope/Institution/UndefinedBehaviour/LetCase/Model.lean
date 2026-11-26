module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LetCase.Model.Defs

public section

namespace Silmaril.Proofs.Isotope.Institution.Refinement.UB.LetCase

open CategoryTheory
open Silmaril.Isotope
open Silmaril.Isotope.Institution.Refinement
open Silmaril.Isotope.Institution.Refinement.UB
open Silmaril.Isotope.Institution.Refinement.UB.LetCase
open Silmaril.Isotope.LetCase.LocallyNameless
open Silmaril.Isotope.Theory (TypingIndex)
open Silmaril.Logic.Institution
open Silmaril.Logic.Metatheory.TheoryModel

universe u

variable {ν τ ε : Type u} [TypeFormers τ] [DecidableEq ν]
attribute [local instance] dialectTyping
variable {P : Institution.InstrSig τ ε} {e : ε} {Γ : Ctx ν τ}

local notation "S" => casePSig P.Instr Γ
local notation "T" => dialectSignature P e Γ

theorem encode_eval (M : OrderedAlgebra (T).sig) {i : TypingIndex τ} (a : Explicit P Γ i) :
    (T).eval M.toAlgebra (encode P e Γ a) =
      (adjoin S).eval (explicitModel P e Γ M).toAlgebra a := by
  let k : nativeAlgebra P e Γ ⟶ (explicitModel P e Γ M).toAlgebra := {
    map := (T).eval M.toAlgebra
    comm := fun o args => match o with
      | none => rfl
      | some o => (Algebra.reductMap (PSig.toSig (relabel P e Γ))
          ((T).isInitial.to M.toAlgebra)).comm o args }
  have h : foldHom (nativeAlgebra P e Γ) ≫ k =
      (adjoin S).isInitial.to (explicitModel P e Γ M).toAlgebra :=
    (adjoin S).isInitial.hom_ext _ _
  exact congrArg (fun m => Algebra.Hom.map m a) h

theorem explicitModel_valid (axioms : Set (Sentence S))
    (M : OrderedAlgebra (T).sig)
    (hM : M ∈ (institution.obj (interpretedSpec P e Γ axioms).sig).modelsOf
      (interpretedSpec P e Γ axioms).axioms) :
    explicitModel P e Γ M ∈ (institution.obj (explicitSpec P Γ axioms).sig).modelsOf
      (explicitSpec P Γ axioms).axioms := by
  intro s hs p hp
  obtain ⟨i, a, b⟩ := p
  have hab : (explicitOrder P Γ axioms).Rel a b := by
    intro N hN q hq
    obtain rfl := List.mem_singleton.1 hq
    exact hN s hs ⟨i, a, b⟩ hp
  have h := (refinement_iff (e := e) axioms _ _).1 hab M hM _ (List.mem_singleton_self _)
  change @LE.le _ ((explicitModel P e Γ M).order i).toLE
    ((adjoin S).eval (explicitModel P e Γ M).toAlgebra a)
    ((adjoin S).eval (explicitModel P e Γ M).toAlgebra b)
  rw [← encode_eval M a, ← encode_eval M b]
  exact h

private theorem relabel_not_fresh {i : TypingIndex τ} (o : (S).sig.Op i) :
    isFresh P e Γ ((PSig.toSig (relabel P e Γ)).op o) = false := by
  cases o <;> rfl

private theorem flag_relabel {i : TypingIndex τ} (a : (S).syn.Carrier i) :
    (T).eval (flagModel P e Γ).toAlgebra ((PSig.translate (relabel P e Γ)).map a) =
      ULift.up false := by
  let σ := PSig.toSig (relabel P e Γ)
  let M := Algebra.reductObj σ (flagModel P e Γ).toAlgebra
  let k : (S).syn ⟶ M := {
    map := fun _ => ULift.up false
    comm := fun o _ => by
      let v (j : Fin ((T).sig.arity (σ.op o))) : ULift.{u} Bool :=
        Eq.rec (motive := fun _ _ => ULift.{u} Bool) (ULift.up false) (σ.argSort o j)
      change ULift.up false =
        ULift.up (max (isFresh P e Γ (σ.op o)) (Finset.univ.sup (fun j => (v j).down)))
      have h : (Finset.univ.sup (fun j => (v j).down)) = false :=
        (Finset.sup_eq_bot_iff _ _).2 (fun j _ =>
          congrArg ULift.down (show v j = ⟨false⟩ from eq_rec_constant _ _))
      rw [relabel_not_fresh, h, max_self] }
  refine ((S).eval_reduct (relabel P e Γ) (flagModel P e Γ).toAlgebra a).symm.trans ?_
  exact congrArg (fun f => Algebra.Hom.map f a) ((S).isInitial.hom_ext _ k)

theorem flag_ub (i : TypingIndex τ) :
    (T).eval (flagModel P e Γ).toAlgebra (nativeUB P e Γ i) = ULift.up true := by
  change Models.denote (flagModel P e Γ).toAlgebra (nativeUB P e Γ i).2 = _
  change ULift.up (max true _) = ULift.up true
  simp

theorem flagModel_valid (axioms : Set (Sentence S)) :
    flagModel P e Γ ∈ (institution.obj (interpretedSpec P e Γ axioms).sig).modelsOf
      (interpretedSpec P e Γ axioms).axioms := by
  intro s hs φ hφ
  rcases hs with ⟨p, _, rfl⟩ | ⟨j, t, rfl⟩
  · obtain ⟨⟨i, x, y⟩, _, rfl⟩ := List.mem_map.1 hφ
    change (T).eval (flagModel P e Γ).toAlgebra ((PSig.translate (relabel P e Γ)).map x) ≤
      (T).eval (flagModel P e Γ).toAlgebra ((PSig.translate (relabel P e Γ)).map y)
    rw [flag_relabel, flag_relabel]
    exact le_rfl
  · obtain rfl := List.mem_singleton.1 hφ
    change (T).eval (flagModel P e Γ).toAlgebra t ≤
      (T).eval (flagModel P e Γ).toAlgebra (nativeUB P e Γ j)
    rw [flag_ub]
    change ((T).eval (flagModel P e Γ).toAlgebra t).down ≤ true
    exact le_top

end Silmaril.Proofs.Isotope.Institution.Refinement.UB.LetCase
