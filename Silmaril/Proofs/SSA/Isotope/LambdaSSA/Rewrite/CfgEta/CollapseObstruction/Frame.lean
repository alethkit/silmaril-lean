module

public import Silmaril.SSA.Isotope.LambdaSSA.Defs

/-! # CFG orbits with coloured divergence -/

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ColouredDivergence

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region

abbrev Val := Value Empty

inductive Result where
  | jump (label : Nat) (value : Val)
  | diverges (colour : Bool)
  | fault

/-- The payload that determines the colour when visited infinitely often. -/
def markedPayload : Val := .inl .unit

abbrev Frame (n : Nat) := Result ⊕ (Fin n × Val)

def enter (n : Nat) : Result → Frame n
  | .jump i v => if h : i < n then .inr (⟨i, h⟩, v) else .inl (.jump (i - n) v)
  | .diverges c => .inl (.diverges c)
  | .fault => .inl .fault

def step {n : Nat} (bs : Fin n → Val → Result) : Frame n → Frame n
  | .inl result => .inl result
  | .inr (i, v) => enter n (bs i v)

def path {n : Nat} (bs : Fin n → Val → Result) (start : Frame n) : Nat → Frame n
  | 0 => start
  | k + 1 => step bs (path bs start k)

theorem path_add {n : Nat} (bs : Fin n → Val → Result) (start : Frame n) (j k : Nat) :
    path bs start (j + k) = path bs (path bs start j) k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (step bs) ih

theorem path_absorb {n : Nat} (bs : Fin n → Val → Result) (r : Result) (k : Nat) :
    path bs (.inl r) k = .inl r := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [path, ih, step]

theorem terminal_unique {n : Nat} (bs : Fin n → Val → Result) (start : Frame n)
    {j k : Nat} {r s : Result} (hr : path bs start j = .inl r) (hs : path bs start k = .inl s) : r = s := by
  rcases Nat.le_total j k with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [path_add, hr, path_absorb] at hs
    exact Sum.inl.inj hs
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [path_add, hs, path_absorb] at hr
    exact (Sum.inl.inj hr).symm

def terminates {n : Nat} (bs : Fin n → Val → Result) (start : Frame n) (r : Result) : Prop :=
  ∃ k, path bs start k = .inl r

def recurrent {n : Nat} (bs : Fin n → Val → Result) (start : Frame n) : Prop :=
  ∀ k, ∃ j ≥ k, ∃ i : Fin n, path bs start j = .inr (i, markedPayload)

/-- A frame that stops returns its terminal outcome. An infinite local orbit
has colour false exactly when it visits the marked payload infinitely often. -/
noncomputable def finish {n : Nat} (bs : Fin n → Val → Result) (start : Frame n) : Result := by
  classical
  exact if h : ∃ r, terminates bs start r then h.choose
    else if recurrent bs start then .diverges false else .diverges true

theorem finish_of_terminal {n : Nat} (bs : Fin n → Val → Result) (start : Frame n)
    {k : Nat} {r : Result} (hr : path bs start k = .inl r) : finish bs start = r := by
  have h : ∃ r, terminates bs start r := ⟨r, k, hr⟩
  rw [finish, dite_eq_left h]
  obtain ⟨j, hj⟩ := h.choose_spec
  exact terminal_unique bs start hj hr

theorem terminates_step_iff {n : Nat} (bs : Fin n → Val → Result)
    (start : Frame n) (r : Result) : terminates bs (step bs start) r ↔ terminates bs start r := by
  have shift (k : Nat) : path bs (step bs start) k = path bs start (1 + k) :=
    (path_add bs start 1 k).symm
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨1 + k, (shift k).symm.trans hk⟩
  · rintro ⟨k, hk⟩
    cases k with
    | zero =>
      change start = .inl r at hk
      exact ⟨0, by rw [hk]; rfl⟩
    | succ k =>
      exact ⟨k, (shift k).trans (by simpa only [Nat.one_add] using hk)⟩

theorem recurrent_step_iff {n : Nat} (bs : Fin n → Val → Result)
    (start : Frame n) : recurrent bs (step bs start) ↔ recurrent bs start := by
  have shift (k : Nat) : path bs (step bs start) k = path bs start (1 + k) :=
    (path_add bs start 1 k).symm
  constructor
  · intro h k
    obtain ⟨j, hj, i, hi⟩ := h k
    exact ⟨1 + j, by omega, i, (shift j).symm.trans hi⟩
  · intro h k
    obtain ⟨j, hj, i, hi⟩ := h (1 + k)
    refine ⟨j - 1, by omega, i, ?_⟩
    rw [shift, show 1 + (j - 1) = j by omega]
    exact hi

theorem finish_step {n : Nat} (bs : Fin n → Val → Result) (start : Frame n) :
    finish bs (step bs start) = finish bs start := by
  classical
  by_cases h : ∃ r, terminates bs start r
  · obtain ⟨r, k, hk⟩ := h
    obtain ⟨j, hj⟩ := (terminates_step_iff bs start r).mpr ⟨k, hk⟩
    rw [finish_of_terminal bs _ hj, finish_of_terminal bs _ hk]
  · have h' : ¬ ∃ r, terminates bs (step bs start) r :=
      fun ⟨r, hr⟩ => h ⟨r, (terminates_step_iff bs start r).mp hr⟩
    rw [finish, dite_eq_right h', finish, dite_eq_right h, recurrent_step_iff]

noncomputable def cfgRun (n : Nat) (bs : Fin n → Val → Result) (entry : Result) : Result :=
  finish bs (enter n entry)

theorem cfgRun_out {n i : Nat} (bs : Fin n → Val → Result) (v : Val) (hi : n ≤ i) :
    cfgRun n bs (.jump i v) = .jump (i - n) v := by
  apply finish_of_terminal bs _ (k := 0)
  simp [path, enter, Nat.not_lt_of_ge hi]

theorem cfgRun_local {n i : Nat} (bs : Fin n → Val → Result) (v : Val) (hi : i < n) :
    cfgRun n bs (.jump i v) = cfgRun n bs (bs ⟨i, hi⟩ v) := by
  change finish bs (enter n (.jump i v)) = _
  rw [enter, dite_eq_left hi, ← finish_step bs (.inr (⟨i, hi⟩, v))]
  rfl

/-- Transform terminal outcomes while preserving each local state. -/
def mapTerminal {n : Nat} (k : Result → Result) : Frame n → Frame n
  | .inl r => .inl (k r)
  | .inr s => .inr s

theorem finish_mapTerminalOn {n : Nat} (bs bs' : Fin n → Val → Result)
    (k : Result → Result) (keep : ∀ c, k (.diverges c) = .diverges c)
    (good : Frame n → Prop) (stable : ∀ s, good s → good (step bs s))
    (comm : ∀ s, good s → step bs' (mapTerminal k s) = mapTerminal k (step bs s))
    (start : Frame n) (hstart : good start) :
    finish bs' (mapTerminal k start) = k (finish bs start) := by
  classical
  have pathGood (i : Nat) : good (path bs start i) := by
    induction i with
    | zero => exact hstart
    | succ i ih => exact stable _ ih
  have paths (i : Nat) : path bs' (mapTerminal k start) i = mapTerminal k (path bs start i) := by
    induction i with
    | zero => rfl
    | succ i ih => rw [path, path, ih, comm _ (pathGood i)]
  by_cases hf : ∃ r, terminates bs start r
  · obtain ⟨r, i, hi⟩ := hf
    have hi' : path bs' (mapTerminal k start) i = .inl (k r) := by
      rw [paths, hi]
      rfl
    rw [finish_of_terminal bs' _ hi', finish_of_terminal bs _ hi]
  · have hf' : ¬ ∃ r, terminates bs' (mapTerminal k start) r := by
      rintro ⟨r, i, hi⟩
      rw [paths] at hi
      cases h : path bs start i with
      | inl r => exact hf ⟨r, i, h⟩
      | inr s => rw [h] at hi; cases hi
    have hre : recurrent bs' (mapTerminal k start) ↔ recurrent bs start := by
      unfold recurrent
      constructor
      · intro h i
        obtain ⟨j, hj, q, hq⟩ := h i
        rw [paths] at hq
        refine ⟨j, hj, q, ?_⟩
        cases he : path bs start j with
        | inl r => rw [he] at hq; cases hq
        | inr s => simpa only [he, mapTerminal] using hq
      · intro h i
        obtain ⟨j, hj, q, hq⟩ := h i
        exact ⟨j, hj, q, by rw [paths, hq]; rfl⟩
    rw [finish, dite_eq_right hf', finish, dite_eq_right hf, hre]
    by_cases h : recurrent bs start <;> simp [h, keep]

theorem finish_mapTerminal {n : Nat} (bs bs' : Fin n → Val → Result)
    (k : Result → Result) (keep : ∀ c, k (.diverges c) = .diverges c)
    (comm : ∀ s, step bs' (mapTerminal k s) = mapTerminal k (step bs s))
    (start : Frame n) : finish bs' (mapTerminal k start) = k (finish bs start) :=
  finish_mapTerminalOn bs bs' k keep (fun _ => True)
    (fun _ _ => trivial) (fun s _ => comm s) start trivial

def mapOut (k : Nat → Val → Result) : Result → Result
  | .jump i v => k i v
  | .diverges c => .diverges c
  | .fault => .fault

def shiftOut (n : Nat) : Result → Result :=
  mapOut (fun i v => .jump (n + i) v)

def insideMap (n : Nat) (k : Nat → Val → Result) : Result → Result :=
  mapOut (fun i v => if i < n then .jump i v else shiftOut n (k (i - n) v))

theorem enter_shiftOut (n : Nat) (r : Result) : enter n (shiftOut n r) = .inl r := by
  cases r with
  | jump i v => simp [shiftOut, mapOut, enter, Nat.not_lt_of_ge (Nat.le_add_right n i)]
  | diverges c => rfl
  | fault => rfl

theorem enter_insideMap (n : Nat) (k : Nat → Val → Result) (r : Result) :
    enter n (insideMap n k r) = mapTerminal (mapOut k) (enter n r) := by
  cases r with
  | jump i v =>
    by_cases h : i < n
    · simp [insideMap, mapOut, enter, mapTerminal, h]
    · rw [insideMap, mapOut, ite_eq_right h, enter_shiftOut, enter, dite_eq_right h]
      rfl
  | diverges c => rfl
  | fault => rfl

theorem cfgRun_mapOut (n : Nat) (bs : Fin n → Val → Result)
    (k : Nat → Val → Result) (r : Result) :
    cfgRun n (fun i v => insideMap n k (bs i v)) (insideMap n k r) =
      mapOut k (cfgRun n bs r) := by
  change finish _ (enter n (insideMap n k r)) = mapOut k (finish bs (enter n r))
  rw [enter_insideMap]
  refine finish_mapTerminal bs _ (mapOut k) (fun _ => rfl) ?_ _
  intro s
  cases s with
  | inl r => rfl
  | inr s =>
    obtain ⟨i, v⟩ := s
    exact enter_insideMap n k (bs i v)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ColouredDivergence
