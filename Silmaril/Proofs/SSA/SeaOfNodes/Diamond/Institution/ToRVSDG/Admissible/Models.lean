module

public import Silmaril.SSA.SeaOfNodes.Diamond.Institution.ToRVSDG.Admissible.Defs

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.Institution.ToRVSDG.AdmissibleProofs

open CategoryTheory Silmaril.Logic.Institution
open RVSDG (Tuple)

universe u v w
variable {Data : Type u} {P Q R : Signature.{u, v} Data}

set_option backward.isDefEq.respectTransparency false in
private theorem induce_extractWithCarriers (m : TargetModel.{u, v, w} P)
    (value : Data → Type w) (carriers : m.value = sortValue value) (law : Admissible m) :
    (extractWithCarriers m value carriers).toRVSDG = m := by
  cases m with
  | mk modelValue state run =>
    change modelValue = sortValue value at carriers
    subst modelValue
    have stateEq : state = (fun s => nomatch s) := funext fun s => nomatch s
    subst state
    unfold extractWithCarriers Diamond.Model.toRVSDG
    congr 1
    funext ins outs op input
    cases op with
    | pure op =>
      change .cons ((run (.pure op) input).get .head) .nil = run (.pure op) input
      cases run (.pure op) input with
      | cons head tail => cases tail; rfl
    | dispatch out =>
      cases input with
      | cons flag captures => exact (law.dispatch out flag captures).symm

theorem induce_extract (m : AdmissibleModel.{u, v, w} P) :
    (extract m).toRVSDG = m.val :=
  induce_extractWithCarriers m.val _ m.property.value_eq m.property

theorem targetCorridor_id (P : Signature.{u, v} Data) :
    targetCorridor.{u, v, w} (𝟙 P) = 𝟙 (targetRoom.{u, v, w} P) := by
  apply Room.hom_ext
  · change (RVSDG.Institution.corridor.{u, max u v, w} (mapSignature (𝟙 P))).sen = id
    rw [mapSignature_id, RVSDG.Institution.corridor_id]
    rfl
  · apply Discrete.functor_ext
    intro m
    apply congrArg Discrete.mk
    apply Subtype.ext
    change RVSDG.Institution.reduct
      (RVSDG.Institution.Signature.opcodeMap (mapSignature (𝟙 P))) m.val = m.val
    rw [mapSignature_id]
    cases m.val
    rfl

theorem targetCorridor_comp (h : P ⟶ Q) (k : Q ⟶ R) :
    targetCorridor.{u, v, w} (h ≫ k) = targetCorridor h ≫ targetCorridor k := by
  apply Room.hom_ext
  · change (RVSDG.Institution.corridor.{u, max u v, w} (mapSignature (h ≫ k))).sen =
      (RVSDG.Institution.corridor.{u, max u v, w} (mapSignature h) ≫ RVSDG.Institution.corridor.{u, max u v, w} (mapSignature k)).sen
    rw [mapSignature_comp, RVSDG.Institution.corridor_comp]
  · apply Discrete.functor_ext
    intro m
    apply congrArg Discrete.mk
    apply Subtype.ext
    change RVSDG.Institution.reduct
      (RVSDG.Institution.Signature.opcodeMap (mapSignature (h ≫ k))) m.val = (reductModel h (reductModel k m)).val
    rw [mapSignature_comp]
    rfl

end Silmaril.SSA.SeaOfNodes.Diamond.Institution.ToRVSDG.AdmissibleProofs
