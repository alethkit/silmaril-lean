module

public import Silmaril.Logic.Temporal.TLA.StutterReduction.Defs
public import Silmaril.Logic.Temporal.TLA.Thms

public section

namespace Silmaril.Proofs.Logic.Temporal.TLA.StutterReduction

open Silmaril.Logic.Temporal.TLA

universe u

variable {S : Type u}

private theorem firstChange_unique {σ : Behavior S} {i j k : Nat}
    (hj : σ.FirstChange i j) (hk : σ.FirstChange i k) : j = k := by
  apply Nat.le_antisymm
  · exact Nat.le_of_not_gt fun h => hk.2.1 (hj.2.2 k (Nat.le_of_lt hk.1) h)
  · exact Nat.le_of_not_gt fun h => hj.2.1 (hk.2.2 j (Nat.le_of_lt hj.1) h)

private theorem firstChange_exists {σ : Behavior S} {i j : Nat} (hij : i ≤ j)
    (h : σ j ≠ σ i) : ∃ k, σ.FirstChange i k := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    classical
    by_cases earlier : ∃ k, i ≤ k ∧ k < j ∧ σ k ≠ σ i
    · obtain ⟨k, hik, hkj, hk⟩ := earlier
      exact ih k hkj hik hk
    · exact ⟨j, Nat.lt_of_le_of_ne hij (fun eq => h (congrArg σ eq.symm)),
        h, fun k hik hkj => Classical.byContradiction fun hk => earlier ⟨k, hik, hkj, hk⟩⟩

private theorem nextChange_of_firstChange {σ : Behavior S} {i j : Nat}
    (h : σ.FirstChange i j) : σ.nextChange i = j := by
  classical
  have existsChange : ∃ k, σ.FirstChange i k := ⟨j, h⟩
  rw [Behavior.nextChange, dite_eq_left existsChange]
  exact firstChange_unique (Classical.choose_spec existsChange) h

private theorem nextChange_of_constant {σ : Behavior S} {i : Nat}
    (h : ∀ j, i ≤ j → σ j = σ i) : σ.nextChange i = i := by
  classical
  rw [Behavior.nextChange]
  exact dite_eq_right fun ⟨j, hj⟩ => hj.2.1 (h j (Nat.le_of_lt hj.1))

private theorem nextChange_cases (σ : Behavior S) (i : Nat) :
    (∃ j, σ.FirstChange i j) ∨ (∀ j, i ≤ j → σ j = σ i) := by
  classical
  by_cases h : ∃ j, i ≤ j ∧ σ j ≠ σ i
  · obtain ⟨j, hij, hj⟩ := h
    exact Or.inl (firstChange_exists hij hj)
  · exact Or.inr fun j hij => Classical.byContradiction fun hj => h ⟨j, hij, hj⟩

private theorem nextChange_suffix (σ : Behavior S) (n i : Nat) :
    n + (σ.suffix n).nextChange i = σ.nextChange (n + i) := by
  rcases nextChange_cases (σ.suffix n) i with ⟨j, hj⟩ | constant
  · have shifted : σ.FirstChange (n + i) (n + j) :=
      ⟨by have := hj.1; omega, hj.2.1, fun k hik hkj => by
        have eq := hj.2.2 (k - n) (by omega) (by omega)
        simpa only [Behavior.suffix, show n + (k - n) = k by omega] using eq⟩
    rw [nextChange_of_firstChange hj, nextChange_of_firstChange shifted]
  · rw [nextChange_of_constant constant, nextChange_of_constant]
    intro k hk
    have eq := constant (k - n) (by omega)
    simpa only [Behavior.suffix, show n + (k - n) = k by omega] using eq

private theorem reduction_at_firstChange {σ : Behavior S} {j : Nat}
    (h : σ.FirstChange 0 j) (n : Nat) :
    σ.canonicalReduction (n + 1) = (σ.suffix j).canonicalReduction n := by
  suffices starts : σ.blockStart (n + 1) = j + (σ.suffix j).blockStart n by
    exact congrArg σ starts
  induction n with
  | zero =>
    simpa only [Behavior.blockStart, Nat.add_zero] using nextChange_of_firstChange h
  | succ n ih =>
    rw [Behavior.blockStart, ih, Behavior.blockStart, nextChange_suffix]

private theorem reduction_constant {σ : Behavior S} (h : ∀ n, σ n = σ 0) :
    σ.canonicalReduction = fun _ => σ 0 :=
  funext fun n => h (σ.blockStart n)

private theorem reduction_at_change {σ : Behavior S} (h : σ 1 ≠ σ 0) :
    σ.canonicalReduction = fun
      | 0 => σ 0
      | n + 1 => (σ.suffix 1).canonicalReduction n := by
  funext n
  cases n with
  | zero => rfl
  | succ n => exact reduction_at_firstChange ⟨by decide, h, fun k _ hk => by
      rw [show k = 0 by omega]⟩ n

theorem canonicalReduction_eq48 : Behavior.SatisfiesLamport48 (S := S)
    Behavior.canonicalReduction := by
  intro σ
  refine ⟨reduction_constant, ?_, reduction_at_change⟩
  rintro ⟨k, hk⟩ same
  obtain ⟨j, hj⟩ := firstChange_exists (Nat.zero_le k) hk
  have later : 1 < j := by
    have positive := hj.1
    by_cases bound : j = 1
    · exact False.elim (hj.2.1 (bound ▸ same))
    · omega
  have tailFirst : (σ.suffix 1).FirstChange 0 (j - 1) := by
    refine ⟨by omega, ?_, fun k _ hk => ?_⟩
    · simpa only [Behavior.suffix, show 1 + (j - 1) = j by omega, Nat.add_zero, same]
        using hj.2.1
    · simpa only [Behavior.suffix, Nat.add_zero, same] using
        hj.2.2 (1 + k) (Nat.zero_le _) (by omega)
  funext n
  cases n with
  | zero => exact same.symm
  | succ n =>
    rw [reduction_at_firstChange hj, reduction_at_firstChange tailFirst]
    have tails : σ.suffix j = (σ.suffix 1).suffix (j - 1) := by
      funext i
      change σ (j + i) = σ (1 + (j - 1 + i))
      rw [show j + i = 1 + (j - 1 + i) by omega]
    rw [← tails]

private theorem eq48_at_firstChange {reduce : Behavior S → Behavior S}
    (h : Behavior.SatisfiesLamport48 reduce) {σ : Behavior S} {i j : Nat}
    (first : σ.FirstChange i j) :
    reduce (σ.suffix i) = fun
      | 0 => σ i
      | n + 1 => reduce (σ.suffix j) n := by
  have tail : (σ.suffix i).suffix 1 = σ.suffix (i + 1) := by
    funext n
    exact congrArg σ (Nat.add_assoc i 1 n).symm
  have inRange := first.1
  by_cases adjacent : i + 1 = j
  · have change : (σ.suffix i) 1 ≠ (σ.suffix i) 0 := by
      simpa only [Behavior.suffix, Nat.add_zero, adjacent] using first.2.1
    have equation := (h (σ.suffix i)).2.2 change
    rw [tail, adjacent] at equation
    funext n
    cases n with
    | zero => exact (congrFun equation 0).trans (congrArg σ (Nat.add_zero i))
    | succ n => exact congrFun equation (n + 1)
  · have same := first.2.2 (i + 1) (by omega) (by omega)
    have differs : ∃ n, (σ.suffix i) n ≠ (σ.suffix i) 0 := by
      refine ⟨j - i, ?_⟩
      simpa only [Behavior.suffix, Nat.add_zero, show i + (j - i) = j by omega] using first.2.1
    have after : σ.FirstChange (i + 1) j := by
      refine ⟨by omega, ?_, fun k hik hkj => ?_⟩
      · rw [same]
        exact first.2.1
      · rw [same]
        exact first.2.2 k (by omega) hkj
    rw [(h (σ.suffix i)).2.1 differs (by simpa only [Behavior.suffix, Nat.add_zero] using same),
      tail, eq48_at_firstChange h after, same]
termination_by j - i

theorem eq_canonicalReduction_of_eq48 {reduce : Behavior S → Behavior S}
    (h : Behavior.SatisfiesLamport48 reduce) : reduce = Behavior.canonicalReduction := by
  have suffixZero (σ : Behavior S) : σ.suffix 0 = σ :=
    funext fun k => congrArg σ (Nat.zero_add k)
  funext σ n
  induction n generalizing σ with
  | zero =>
    rcases nextChange_cases σ 0 with ⟨j, hj⟩ | constant
    · simpa only [suffixZero, Behavior.blockStart, Behavior.canonicalReduction] using
        congrFun (eq48_at_firstChange h hj) 0
    · exact congrFun ((h σ).1 (fun i => constant i (Nat.zero_le i))) 0
  | succ n ih =>
    rcases nextChange_cases σ 0 with ⟨j, hj⟩ | constant
    · have eq := congrFun (eq48_at_firstChange h hj) (n + 1)
      rw [suffixZero] at eq
      exact eq.trans ((ih (σ.suffix j)).trans (reduction_at_firstChange hj n).symm)
    · exact (congrFun ((h σ).1 (fun i => constant i (Nat.zero_le i))) (n + 1)).trans
        (constant _ (Nat.zero_le _)).symm

private theorem index_mono {index : Nat → Nat} (step : ∀ i, index i ≤ index (i + 1))
    {i j : Nat} (h : i ≤ j) : index i ≤ index j := by
  induction h with
  | refl => exact Nat.le_refl _
  | @step j _ ih => exact Nat.le_trans ih (step j)

private theorem retiming_mono (r : Retiming) {i j : Nat} (h : i ≤ j) :
    r.index i ≤ r.index j :=
  index_mono (fun k => (r.step k).elim (fun h => by omega) (fun h => by omega)) h

private theorem nextChange_retime (σ : Behavior S) (r : Retiming) (i : Nat) :
    r.index ((σ.retime r).nextChange i) = σ.nextChange (r.index i) := by
  rcases nextChange_cases σ (r.index i) with ⟨j, first⟩ | constant
  · have later := first.1
    obtain ⟨k, hik, hk, hk'⟩ := r.crosses (i := i) (j := j - 1) (by omega)
    have atChange : r.index (k + 1) = j := by omega
    have firstExpanded : (σ.retime r).FirstChange i (k + 1) := by
      refine ⟨by omega, ?_, fun l hil hlk => ?_⟩
      · simpa only [Behavior.retime, atChange] using first.2.1
      · have bound := retiming_mono r (show l ≤ k by omega)
        exact first.2.2 (r.index l) (retiming_mono r hil) (by omega)
    rw [nextChange_of_firstChange firstExpanded, nextChange_of_firstChange first, atChange]
  · have constantExpanded (k : Nat) (hik : i ≤ k) : (σ.retime r) k = (σ.retime r) i :=
      constant (r.index k) (retiming_mono r hik)
    rw [nextChange_of_constant constantExpanded, nextChange_of_constant constant]

theorem canonicalReduction_retime (σ : Behavior S) (r : Retiming) :
    (σ.retime r).canonicalReduction = σ.canonicalReduction := by
  funext n
  have starts : r.index ((σ.retime r).blockStart n) = σ.blockStart n := by
    induction n with
    | zero => exact r.zero
    | succ n ih => rw [Behavior.blockStart, nextChange_retime, ih, Behavior.blockStart]
  exact congrArg σ starts

/-- Count changes before the final block, then advance at every instant in the
constant tail so that the clock remains cofinal. -/
private noncomputable def reductionClock (σ : Behavior S) : Nat → Nat
  | 0 => 0
  | i + 1 =>
    open Classical in
    if σ (i + 1) ≠ σ i ∨ (∀ j, i ≤ j → σ j = σ i) then reductionClock σ i + 1
    else reductionClock σ i

private theorem clock_step (σ : Behavior S) (i : Nat) :
    reductionClock σ (i + 1) = reductionClock σ i ∨
      reductionClock σ (i + 1) = reductionClock σ i + 1 := by
  rw [reductionClock]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

private theorem clock_mono (σ : Behavior S) {i j : Nat} (h : i ≤ j) :
    reductionClock σ i ≤ reductionClock σ j :=
  index_mono (fun k => (clock_step σ k).elim (fun h => by omega) (fun h => by omega)) h

private theorem clock_progress (σ : Behavior S) (i : Nat) :
    ∃ k, reductionClock σ i < reductionClock σ k := by
  obtain ⟨k, hik, advance⟩ :
      ∃ k, i ≤ k ∧ (σ (k + 1) ≠ σ k ∨ (∀ j, k ≤ j → σ j = σ k)) := by
    rcases nextChange_cases σ i with ⟨j, first⟩ | constant
    · have later := first.1
      refine ⟨j - 1, by omega, Or.inl ?_⟩
      rw [show j - 1 + 1 = j by omega, first.2.2 (j - 1) (by omega) (by omega)]
      exact first.2.1
    · exact ⟨i, Nat.le_refl _, Or.inr constant⟩
  refine ⟨k + 1, ?_⟩
  rw [reductionClock, ite_eq_left advance]
  exact Nat.lt_succ_of_le (clock_mono σ hik)

private noncomputable def reductionRetiming (σ : Behavior S) : Retiming where
  index := reductionClock σ
  zero := rfl
  step := clock_step σ
  cofinal j := by
    induction j with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ j ih =>
      obtain ⟨i, hi⟩ := ih
      obtain ⟨k, hk⟩ := clock_progress σ i
      exact ⟨k, by omega⟩

private theorem clock_within_block (σ : Behavior S) (i : Nat) :
    let start := σ.blockStart (reductionClock σ i)
    start ≤ i ∧ ∀ k, start ≤ k → k ≤ i → σ k = σ start := by
  induction i with
  | zero =>
    exact ⟨Nat.le_refl _, fun k _ hk => congrArg σ (Nat.eq_zero_of_le_zero hk)⟩
  | succ i ih =>
    classical
    let start := σ.blockStart (reductionClock σ i)
    obtain ⟨startLe, agrees⟩ := ih
    have current : σ i = σ start := agrees i startLe (Nat.le_refl _)
    by_cases changed : σ (i + 1) ≠ σ i
    · have first : σ.FirstChange start (i + 1) :=
        ⟨by omega, by rwa [← current], fun k hk hk' => agrees k hk (by omega)⟩
      dsimp only
      rw [reductionClock, ite_eq_left (Or.inl changed), Behavior.blockStart,
        nextChange_of_firstChange first]
      exact ⟨Nat.le_refl _, fun k h₁ h₂ => congrArg σ (Nat.le_antisymm h₂ h₁)⟩
    · have same : σ (i + 1) = σ i := Classical.byContradiction changed
      have extended : start ≤ i + 1 ∧ ∀ k, start ≤ k → k ≤ i + 1 → σ k = σ start :=
        ⟨by omega, fun k hk hk' => by
          by_cases last : k = i + 1
          · exact (congrArg σ last).trans (same.trans current)
          · exact agrees k hk (by omega)⟩
      dsimp only
      by_cases constant : ∀ j, i ≤ j → σ j = σ i
      · have constantFromStart (k : Nat) (hk : start ≤ k) : σ k = σ start := by
          by_cases early : k ≤ i
          · exact agrees k hk early
          · exact (constant k (by omega)).trans current
        rw [reductionClock, ite_eq_left (Or.inr constant), Behavior.blockStart,
          nextChange_of_constant constantFromStart]
        exact extended
      · rw [reductionClock, ite_eq_right (fun h => h.elim changed constant)]
        exact extended

private theorem reduction_expands (σ : Behavior S) :
    σ.canonicalReduction.retime (reductionRetiming σ) = σ :=
  funext fun i => ((clock_within_block σ i).2 i (clock_within_block σ i).1 (Nat.le_refl _)).symm

theorem canonicalReduction_of_reduced (σ : Behavior S)
    (h : ∀ i, σ (i + 1) = σ i → ∀ j, i ≤ j → σ j = σ i) :
    σ.canonicalReduction = σ := by
  have clock_id (i : Nat) : reductionClock σ i = i := by
    induction i with
    | zero => rfl
    | succ i ih =>
      have advances : σ (i + 1) ≠ σ i ∨ (∀ j, i ≤ j → σ j = σ i) := by
        by_cases same : σ (i + 1) = σ i
        · exact Or.inr (h i same)
        · exact Or.inl same
      rw [reductionClock, ite_eq_left advances, ih]
  funext i
  have eq := congrFun (reduction_expands σ) i
  simpa only [Behavior.retime, reductionRetiming, clock_id] using eq

theorem canonicalReduction_eq_iff_stutterEquiv (σ τ : Behavior S) :
    σ.canonicalReduction = τ.canonicalReduction ↔ StutterEquiv σ τ := by
  constructor
  · intro eq
    have equivalent (ρ : Behavior S) : StutterEquiv ρ.canonicalReduction ρ := by
      have expanded := StutterEquiv.retime ρ.canonicalReduction (reductionRetiming ρ)
      rw [reduction_expands] at expanded
      exact expanded
    have left : StutterEquiv σ τ.canonicalReduction := eq ▸ (equivalent σ).symm
    exact left.trans (equivalent τ)
  · rintro ⟨r, t, agrees⟩
    rw [← canonicalReduction_retime σ r, ← canonicalReduction_retime τ t, agrees]

end Silmaril.Proofs.Logic.Temporal.TLA.StutterReduction
