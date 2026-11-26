module

public import Silmaril.SSA.Peggy.EPEG.Saturation.Defs
import Silmaril.SSA.Peggy.EPEG.Thms

public section

namespace Silmaril.Proofs.SSA.Peggy.EPEG.Saturation

open Silmaril.SSA
open Silmaril.SSA.Peggy.EPEG
open Silmaril.SSA.Peggy.EPEG.Saturation
open RVSDG (Tuple)

universe u v x

variable {Data : Type u} {P : PEG.InstructionSet.{u,v} Data}
variable {params results : List (PEG.Ty Data)} {n l : Nat}
variable {g : PEG.Graph P params results n l}
variable {m : PEG.Interpretation.{u,v,x} P} {values : g.Valuation m} {env : Tuple m.Value params}

private theorem enabled_iff {o : Obligation g} {c : Classes n} :
    o.enabled c = true ↔ o.check c = true ∧ c o.endpoints.1 ≠ c o.endpoints.2 := by
  simp [Obligation.enabled]

private theorem check_mono {c d : Classes n} (h : Refines c d) (o : Obligation g)
    (valid : o.check c = true) : o.check d = true := by
  cases o with
  | guarded rule =>
    apply List.all_eq_true.mpr
    intro guard mem
    exact beq_iff_eq.mpr (h _ _ (beq_iff_eq.mp (List.all_eq_true.mp valid guard mem)))
  | congruent pair =>
    apply List.all_eq_true.mpr
    intro slot mem
    exact beq_iff_eq.mpr (h _ _ (beq_iff_eq.mp (List.all_eq_true.mp valid slot mem)))

private theorem merge_below {c d : Classes n} {a b : Fin n}
    (below : Refines c d) (joins : d a = d b) : Refines (c.merge a b) d := by
  let rep p := if c p = c b then a else p
  have moved (p : Fin n) : d p = d (rep p) := by
    dsimp only [rep]
    split
    next h => exact (below _ _ h).trans joins.symm
    next => rfl
  intro p q same
  exact (moved p).trans ((below (rep p) (rep q) same).trans (moved q).symm)

private theorem take_some {c : Classes n} {os rest : List (Obligation g)} {picked : Obligation g}
    (found : takeEnabled c os = some (picked, rest)) :
    picked.enabled c = true ∧ List.Perm (picked :: rest) os := by
  induction os generalizing picked rest with
  | nil => simp [takeEnabled] at found
  | cons o os ih =>
    cases active : o.enabled c with
    | true =>
      simp only [takeEnabled, active, ite_true, Option.some.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, rfl⟩ := found
      exact ⟨active, .refl _⟩
    | false =>
      cases next : takeEnabled c os with
      | none => simp [takeEnabled, active, next] at found
      | some pair =>
        obtain ⟨later, tail⟩ := pair
        simp [takeEnabled, active, next] at found
        obtain ⟨rfl, rfl⟩ := found
        obtain ⟨enabled, perm⟩ := ih next
        exact ⟨enabled, (List.Perm.swap o later tail).trans (perm.cons o)⟩

private theorem take_none {c : Classes n} {os : List (Obligation g)}
    (missing : takeEnabled c os = none) : ∀ o ∈ os, o.enabled c = false := by
  induction os with
  | nil => simp
  | cons first os ih =>
    have inactive : first.enabled c = false := by
      cases active : first.enabled c
      · rfl
      · simp [takeEnabled, active] at missing
    have tail : takeEnabled c os = none := by
      cases next : takeEnabled c os
      · rfl
      · simp [takeEnabled, inactive, next] at missing
    intro o mem
    rcases List.mem_cons.mp mem with rfl | mem
    · exact inactive
    · exact ih tail o mem

private theorem closed_of_inactive {os : List (Obligation g)} {c : Classes n}
    (inactive : ∀ o ∈ os, o.enabled c = false) : Closed os c := by
  intro o mem check
  by_contra distinct
  have active := enabled_iff.mpr ⟨check, distinct⟩
  have off := inactive o mem
  simp [active] at off

theorem isClosed_iff {os : List (Obligation g)} {c : Classes n} :
    isClosed os c = true ↔ Closed os c := by
  constructor
  · intro check
    apply closed_of_inactive
    intro o mem
    simpa using List.all_eq_true.mp check o mem
  · intro h
    apply List.all_eq_true.mpr
    intro o mem
    cases checked : o.enabled c
    · rfl
    · obtain ⟨check, different⟩ := enabled_iff.mp checked
      exact (different (h o mem check)).elim

theorem run_extends (fuel : Nat) (os : List (Obligation g)) (c : Classes n) :
    Refines c (run fuel os c) := by
  induction fuel generalizing os c with
  | zero => exact fun _ _ h => h
  | succ fuel ih =>
    cases next : takeEnabled c os with
    | none => simpa only [run, next] using (show Refines c c from fun _ _ h => h)
    | some pair =>
      obtain ⟨o, rest⟩ := pair
      rw [run, next]
      exact fun p q h => ih rest (o.merge c) p q (c.merge_preserves _ _ h)

theorem run_mono_fuel {small large : Nat} (bound : small ≤ large)
    (os : List (Obligation g)) (c : Classes n) : Refines (run small os c) (run large os c) := by
  induction small generalizing large os c with
  | zero => exact run_extends large os c
  | succ small ih =>
    cases large with
    | zero => exact (Nat.not_succ_le_zero _ bound).elim
    | succ large =>
      cases next : takeEnabled c os with
      | none => simp only [run, next]; exact fun _ _ h => h
      | some selected =>
        obtain ⟨o, rest⟩ := selected
        simp only [run, next]
        exact ih (Nat.le_of_succ_le_succ bound) rest (o.merge c)

theorem run_below (fuel : Nat) (os : List (Obligation g)) {c d : Classes n}
    (below : Refines c d) (closed : Closed os d) : Refines (run fuel os c) d := by
  induction fuel generalizing os c with
  | zero => exact below
  | succ fuel ih =>
    cases next : takeEnabled c os with
    | none => simpa only [run, next] using below
    | some pair =>
      obtain ⟨o, rest⟩ := pair
      obtain ⟨active, perm⟩ := take_some next
      rw [run, next]
      apply ih rest
      · apply merge_below below
        exact closed o (perm.mem_iff.mp List.mem_cons_self) (check_mono below o (enabled_iff.mp active).1)
      · exact fun p h => closed p (perm.mem_iff.mp (List.mem_cons_of_mem _ h))

theorem run_closed (fuel : Nat) (os : List (Obligation g)) (c : Classes n)
    (enough : os.length ≤ fuel) : Closed os (run fuel os c) := by
  induction fuel generalizing os c with
  | zero =>
    have noItems : os = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst os
    exact fun _ mem => (List.not_mem_nil mem).elim
  | succ fuel ih =>
    cases next : takeEnabled c os with
    | none =>
      rw [run, next]
      exact closed_of_inactive (take_none next)
    | some pair =>
      obtain ⟨o, rest⟩ := pair
      obtain ⟨_, perm⟩ := take_some next
      have lengths := perm.length_eq
      simp only [List.length_cons] at lengths
      have tailClosed := ih rest (o.merge c) (by omega)
      rw [run, next]
      intro p mem checked
      rcases List.mem_cons.mp (perm.mem_iff.mpr mem) with same | tail
      · subst p
        exact run_extends fuel rest (o.merge c) _ _ (c.merge_equates _ _)
      · exact tailClosed p tail checked

theorem saturate_perm {os ps : List (Obligation g)} (perm : List.Perm os ps) (c : Classes n)
    (a b : Fin n) : saturate os c a = saturate os c b ↔ saturate ps c a = saturate ps c b := by
  have left := run_closed os.length os c (Nat.le_refl _)
  have right := run_closed ps.length ps c (Nat.le_refl _)
  constructor
  · exact run_below os.length os (run_extends ps.length ps c)
      (fun o h => right o (perm.mem_iff.mp h)) a b
  · exact run_below ps.length ps (run_extends os.length os c)
      (fun o h => left o (perm.mem_iff.mpr h)) a b

private theorem fire_sound (o : Obligation g) {c : Classes n}
    (solves : g.Solves m env values) (valid : c.Valid values)
    (contract : o.Holds values) (checked : o.check c = true) : (o.merge c).Valid values := by
  cases o with
  | guarded rule => exact rule.merge_sound valid contract checked
  | congruent pair => exact pair.merge_sound solves valid checked

theorem run_sound (fuel : Nat) (os : List (Obligation g)) {c : Classes n}
    (solves : g.Solves m env values) (valid : c.Valid values)
    (contracts : ∀ o ∈ os, o.Holds values) : (run fuel os c).Valid values := by
  induction fuel generalizing os c with
  | zero => exact valid
  | succ fuel ih =>
    cases next : takeEnabled c os with
    | none => simpa only [run, next] using valid
    | some pair =>
      obtain ⟨o, rest⟩ := pair
      obtain ⟨active, perm⟩ := take_some next
      rw [run, next]
      apply ih rest
      · exact fire_sound o solves valid (contracts o (perm.mem_iff.mp List.mem_cons_self))
          (enabled_iff.mp active).1
      · exact fun p h => contracts p (perm.mem_iff.mp (List.mem_cons_of_mem _ h))

end Silmaril.Proofs.SSA.Peggy.EPEG.Saturation
