module

public import Silmaril.SSA.PEG.Builder

public section

namespace Silmaril.SSA.PEG.Proofs

open RVSDG (Tuple)

universe u v

variable {Data : Type u} [DecidableEq Data] {n l : Nat} {sort : Fin n → Ty Data}
variable {P : InstructionSet.{u,v} Data} {params results ts : List (Ty Data)}

private theorem checkRef_roundTrip {t : Ty Data} (r : Ref sort t) :
    Ref.check sort t r.id.val = some r := by
  obtain ⟨⟨i, bound⟩, typed⟩ := r
  simp [Ref.check, bound, typed]

private theorem checkRef_number {i : Nat} {t : Ty Data} {r : Ref sort t}
    (h : Ref.check sort t i = some r) : r.id.val = i := by
  unfold Ref.check at h
  split at h <;> try contradiction
  split at h <;> cases h
  rfl

theorem checkRefs_roundTrip (rs : Tuple (Ref sort) ts) :
    checkRefs sort ts (refNumbers rs) = some rs := by
  induction rs with
  | nil => rfl
  | cons r _ ih => simp [checkRefs, refNumbers, checkRef_roundTrip r, ih]

theorem checkRefs_numbers {is : List Nat} {rs : Tuple (Ref sort) ts}
    (h : checkRefs sort ts is = some rs) : refNumbers rs = is := by
  induction rs generalizing is with
  | nil => cases is <;> simp_all [checkRefs, refNumbers]
  | @cons t ts r rs ih =>
    cases is with
    | nil => contradiction
    | cons i is =>
      unfold checkRefs at h
      cases h₁ : Ref.check sort t i <;> simp [h₁] at h
      cases h₂ : checkRefs sort ts is <;> simp [h₂] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [refNumbers, checkRef_number h₁, ih h₂]

theorem check_roundTrip (g : Graph P params results n l) :
    g.toRaw.check = some g := by
  cases g
  simp [Graph.toRaw, RawGraph.check, checkRefs_roundTrip, Node.ofLabel]

theorem toRaw_of_check {raw : RawGraph P params results n l} {g : Graph P params results n l}
    (h : raw.check = some g) : g.toRaw = raw := by
  unfold RawGraph.check at h
  split at h
  · contradiction
  · rename_i roots checked
    split at h
    · rename_i ok
      cases h
      have rows : ∀ i, refNumbers ((checkRefs raw.sort (raw.node i).inputs (raw.node i).args).get
          (ok i)) = (raw.node i).args := fun i =>
        checkRefs_numbers (Option.some_get (ok i)).symm
      cases raw with
      | mk forest sort node rootIds =>
        simp [Graph.toRaw, Node.ofLabel, checkRefs_numbers checked, rows]
    · contradiction

end Silmaril.SSA.PEG.Proofs
