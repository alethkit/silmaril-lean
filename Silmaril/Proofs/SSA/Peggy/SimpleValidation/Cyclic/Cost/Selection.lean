module

public import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Defs

public section

namespace Silmaril.Proofs.SSA.Peggy.SimpleValidation.Cyclic.Cost

open Silmaril.SSA.PEG
open Silmaril.SSA.Peggy.EPEG (Classes)
open Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params : List (Ty Data)} {result : Ty Data} {n : Nat}
variable {source : Graph P params [result] n 1} {classes : Classes n}
variable [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
variable {cost : Candidate source → Nat} {pool : List (Candidate source)}
variable {chosen : Accepted source classes}

private theorem check_candidate {candidate : Candidate source} {a : Accepted source classes}
    (checked : candidate.check classes = some a) : a.candidate = candidate := by
  unfold Candidate.check at checked
  split at checked
  · cases checked
  · obtain ⟨_, _, eq⟩ := Option.map_eq_some_iff.mp checked
    exact congrArg Accepted.candidate eq.symm

theorem selected (found : select classes cost pool = some chosen) :
    chosen.candidate ∈ pool ∧ chosen.candidate.check classes = some chosen := by
  obtain ⟨candidate, member, checked⟩ := List.mem_filterMap.mp (List.minOn?_mem found)
  rw [check_candidate checked]
  exact ⟨member, checked⟩

theorem minimal (found : select classes cost pool = some chosen) {other : Candidate source}
    (member : other ∈ pool) (admitted : (other.check classes).isSome = true) :
    cost chosen.candidate ≤ cost other := by
  obtain ⟨a, checked⟩ := Option.isSome_iff_exists.mp admitted
  have kept : a ∈ pool.filterMap (Candidate.check classes) :=
    List.mem_filterMap.mpr ⟨other, member, checked⟩
  unfold select at found
  simpa [found, check_candidate checked] using
    List.apply_get_minOn?_le_of_mem (f := fun a => cost a.candidate) kept

theorem select_none :
    select classes cost pool = none ↔ ∀ candidate ∈ pool, candidate.check classes = none := by
  rw [← Option.isNone_iff_eq_none]
  simp [select, Option.isNone_iff_eq_none, List.minOn?_eq_ite]

end Silmaril.Proofs.SSA.Peggy.SimpleValidation.Cyclic.Cost
