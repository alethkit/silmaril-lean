module

public import Silmaril.Semantics.RuntimeWires.SeamTrace.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.Set.Function

public section

namespace Silmaril.RuntimeWires.Proofs.SeamTrace

open Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O}

theorem row_addresses (row first : ℕ) (boxes : List (BoxTrace S)) :
    (addressBoxes row first boxes).map Prod.fst =
      (List.range' first boxes.length).map (fun i => (row, i)) := by
  induction boxes generalizing first with
  | nil => rfl
  | cons box boxes ih => simp [addressBoxes, List.range'_succ, ih]

theorem mem_row_addresses {row first : ℕ} {boxes : List (BoxTrace S)} {site : BoxAddress} :
    site ∈ (addressBoxes row first boxes).map Prod.fst ↔
      site.1 = row ∧ first ≤ site.2 ∧ site.2 < first + boxes.length := by
  rw [row_addresses, List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨rfl, List.mem_range'_1.mp hi⟩
  · rintro ⟨h, bounds⟩
    exact ⟨site.2, List.mem_range'_1.mpr bounds, Prod.ext h.symm rfl⟩

private theorem addressRows_le (row : ℕ) (rows : List (List (BoxTrace S))) {site : BoxAddress}
    (mem : site ∈ (addressRows row rows).map Prod.fst) : row ≤ site.1 := by
  induction rows generalizing row with
  | nil => simp [addressRows] at mem
  | cons boxes rows ih =>
    simp only [addressRows, List.map_append, List.mem_append] at mem
    exact mem.elim (fun h => (mem_row_addresses.mp h).1.ge)
      (fun h => (Nat.le_succ _).trans (ih _ h))

theorem addresses_nodup (row : ℕ) (rows : List (List (BoxTrace S))) :
    ((addressRows row rows).map Prod.fst).Nodup := by
  induction rows generalizing row with
  | nil => exact .nil
  | cons boxes rest ih =>
    rw [addressRows, List.map_append, List.nodup_append']
    refine ⟨?_, ih _, List.disjoint_left.mpr (fun site head tail => ?_)⟩
    · rw [row_addresses, List.nodup_map_iff (fun _ _ h => congrArg Prod.snd h)]
      exact List.nodup_range'
    · have eq := (mem_row_addresses.mp head).1
      have bound := addressRows_le (row + 1) rest tail
      omega

theorem route_bijOn {left right : SheetTrace S} {route : BoxAddress → BoxAddress}
    (matchTrace : left.Renamed right route) :
    Set.BijOn route left.boxAddresses right.boxAddresses := by
  have keys : ((left.occurrences.map Prod.fst).map route).Perm (right.occurrences.map Prod.fst) := by
    simpa only [SheetTrace.occurrences, List.map_map, Function.comp_def, BoxOccurrence.rename] using
      matchTrace.occurrences.map Prod.fst
  have nd : ((left.occurrences.map Prod.fst).map route).Nodup :=
    keys.nodup_iff.mpr (addresses_nodup 0 right.rows)
  refine ⟨?_, (List.nodup_map_iff_inj_on (addresses_nodup 0 left.rows)).mp nd, ?_⟩
  · intro x hx
    exact keys.mem_iff.mp (List.mem_map.mpr ⟨x, hx, rfl⟩)
  · intro y hy
    exact List.mem_map.mp (keys.mem_iff.mpr hy)

end Silmaril.RuntimeWires.Proofs.SeamTrace
