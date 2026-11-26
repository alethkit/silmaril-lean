module

public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Flat.Thms

/-! # Erasure of typed labels and their payloads -/

public section

universe u

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed
open Silmaril.Isotope.Semantics (encodeValue encodeValue_injective)
open Monadic (LabelValue)

variable {κ : Type u} [AtomValues κ]

attribute [local instance] typeModel

local notation "V" => AtomValues.carrier (κ := κ)

private theorem encode_cast {A B : Ty κ} (eq : A = B) (a : Ty.denote V A) :
    encodeValue V B (eq ▸ a) = encodeValue V A a := by cases eq; rfl

private theorem encode_cast_type {A B : Ty κ} (eq : A = B)
    (castEq : Ty.denote V A = Ty.denote V B) (a : Ty.denote V A) :
    encodeValue V B (cast castEq a) = encodeValue V A a := by
  cases eq
  rfl

@[simp] theorem encodeLabel_inject {L : LCtx (Ty κ)} {A : Ty κ}
    (i : Nat) (h : At L i A) (a : Ty.denote V A) :
    encodeLabel L (LabelValue.inject i h a) = (i, encodeValue V A a) := by
  unfold encodeLabel
  rw [LabelValue.toSigma_inject]
  obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp h
  change (i, encodeValue V L[i] (he.symm ▸ a)) = _
  rw [encode_cast]

theorem encodeLabel_injective (L : LCtx (Ty κ)) : Function.Injective (encodeLabel L) := by
  intro a b h
  apply (LabelValue.sigmaEquiv L).injective
  change LabelValue.toSigma L a = LabelValue.toSigma L b
  rcases ha : LabelValue.toSigma L a with ⟨i, x⟩
  rcases hb : LabelValue.toSigma L b with ⟨j, y⟩
  rw [encodeLabel, encodeLabel, ha, hb] at h
  have he : i = j := Fin.ext (congrArg Prod.fst h)
  subst j
  have eq : x = y := encodeValue_injective V _ (congrArg Prod.snd h)
  rw [eq]

theorem encodeBlock_split {n : Nat} (R : Fin n → Ty κ) (L : LCtx (Ty κ))
    (x : LabelValue (List.ofFn R ++ L)) :
    Sum.map (encodeLabel L) (encodeBlock ∘ Monadic.labelDenToFinite R)
      (LabelValue.appendSplit (List.ofFn R) L x) =
      splitTransfer n (encodeLabel (List.ofFn R ++ L) x) := by
  have eq := LabelValue.appendSplit_toSigma (List.ofFn R) L x
  cases hs : LabelValue.appendSplit (List.ofFn R) L x with
  | inl out =>
    rw [hs] at eq
    rcases ho : LabelValue.toSigma L out with ⟨i, a⟩
    dsimp only at eq
    rw [ho] at eq
    have he : ((List.ofFn R ++ L).get (Fin.cast List.length_append.symm
        (Fin.natAdd (List.ofFn R).length i))) = L.get i := by simp
    rw [Sum.map_inl, encodeLabel, encodeLabel, eq, ho]
    have encoded :
        encodeSigma (List.ofFn R ++ L) (LabelValue.sigmaExternal (List.ofFn R) L ⟨i, a⟩) =
          (n + i.val, encodeValue V (L.get i) a) := by
      refine Prod.ext (by simp [encodeSigma, LabelValue.sigmaExternal]) ?_
      exact encode_cast_type he.symm _ a
    rw [encoded]
    simp [encodeSigma, splitTransfer, show ¬ n + i.val < n by omega]
  | inr inside =>
    rw [hs] at eq
    rcases hi : LabelValue.toSigma (List.ofFn R) inside with ⟨j, a⟩
    dsimp only at eq
    rw [hi] at eq
    let i : Fin n := ⟨j, by simpa using j.isLt⟩
    have hAt : At (List.ofFn R) i.val (R i) := SSA.FiniteSum.at_ofFn R i
    have hType : (List.ofFn R).get j = R i := by simp [i]
    have hinj : inside = LabelValue.inject i.val hAt (hType ▸ a) := by
      apply (LabelValue.sigmaEquiv (List.ofFn R)).injective
      change LabelValue.toSigma (List.ofFn R) inside =
        LabelValue.toSigma (List.ofFn R) (LabelValue.inject i.val hAt (hType ▸ a))
      rw [hi, LabelValue.toSigma_inject]
      apply Sigma.ext
      · rfl
      · dsimp only [LabelValue.sigmaInject]
        have hback : R i = (List.ofFn R).get j := hType.symm
        change HEq a (hback ▸ (hType ▸ a))
        exact (eqRec_heq hType a).symm.trans (eqRec_heq hback (hType ▸ a)).symm
    rw [Sum.map_inr, Function.comp_apply, hinj, Monadic.labelDenToFinite_recursiveInject]
    rw [encodeLabel, eq]
    have he : (List.ofFn R ++ L).get (Fin.castLE (by simp) j) = (List.ofFn R).get j := by
      exact List.getElem_append_left j.isLt
    have encoded :
        encodeSigma (List.ofFn R ++ L) (LabelValue.sigmaLocal (List.ofFn R) L ⟨j, a⟩) =
          (j.val, encodeValue V ((List.ofFn R).get j) a) := by
      refine Prod.ext rfl ?_
      exact encode_cast_type he.symm _ a
    rw [encoded]
    have hlt : j.val < n := i.isLt
    simp [encodeBlock, Monadic.finiteLabelInject, splitTransfer, hlt, encode_cast, i]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed
