module

public import Silmaril.Formats.Sqlite.Varint.Defs

public section

namespace Silmaril.Proofs.Formats.Sqlite.Varint

open Silmaril.Formats Silmaril.Formats.Sqlite Silmaril.Formats.Sqlite.Varint

private theorem last_progress (view : File.View) (offset acc value next : Nat)
    (parsed : readAux? view 1 offset acc = some (value,next)) :
    offset < next ∧ next ≤ offset+1 := by
  cases byte : view.get? offset with
  | none => simp [readAux?, byte] at parsed
  | some b =>
    have reduced : some (acc*256+b.toNat,offset+1) = some (value,next) := by
      unfold readAux? at parsed
      rw [byte] at parsed
      exact parsed
    have consumed : offset+1 = next := congrArg Prod.snd (Option.some.inj reduced)
    exact ⟨by omega, by omega⟩

private theorem step_progress (view : File.View) (fuel offset acc value next : Nat)
    (ih : ∀ offset acc value next, readAux? view (fuel+1) offset acc = some (value,next) →
      offset < next ∧ next ≤ offset+(fuel+1))
    (parsed : readAux? view (fuel+2) offset acc = some (value,next)) :
    offset < next ∧ next ≤ offset+(fuel+2) := by
  cases byte : view.get? offset with
  | none => simp [readAux?,byte] at parsed
  | some b =>
    have reduced : (if b.toNat < 128 then some (acc*128+b.toNat%128,offset+1)
        else readAux? view (fuel+1) (offset+1) (acc*128+b.toNat%128)) = some (value,next) := by
      unfold readAux? at parsed
      rw [byte] at parsed
      exact parsed
    split at reduced
    next terminal =>
      have consumed : offset+1 = next := congrArg Prod.snd (Option.some.inj reduced)
      exact ⟨by omega, by omega⟩
    next continued =>
      have progress : offset+1 < next ∧ next ≤ offset+1+(fuel+1) := ih _ _ _ _ reduced
      exact ⟨by omega, by omega⟩

theorem readAux?_progress (view : File.View) (fuel offset acc value next : Nat)
    (parsed : readAux? view fuel offset acc = some (value,next)) :
    offset < next ∧ next ≤ offset + fuel := by
  induction fuel generalizing offset acc value next with
  | zero => simp [readAux?] at parsed
  | succ fuel ih =>
    cases fuel with
    | zero => exact last_progress view offset acc value next parsed
    | succ fuel => exact step_progress view fuel offset acc value next ih parsed

theorem read?_progress (view : File.View) (offset next : Nat) (value : UInt64)
    (parsed : read? view offset = some (value,next)) :
    offset < next ∧ next ≤ offset + 9 := by
  unfold read? at parsed
  cases hn : readNat? view offset with
  | none => simp [hn] at parsed
  | some pair =>
    obtain ⟨n,k⟩ := pair
    simp only [hn, Option.map_some, Option.some.injEq, Prod.mk.injEq] at parsed
    obtain ⟨_,rfl⟩ := parsed
    exact readAux?_progress view 9 offset 0 n k hn

end Silmaril.Proofs.Formats.Sqlite.Varint
