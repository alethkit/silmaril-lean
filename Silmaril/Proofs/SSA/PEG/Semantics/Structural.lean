module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Find
public import Mathlib.Order.WellFounded
public import Silmaril.SSA.PEG.Semantics.Demand
public import Silmaril.SSA.PEG.Thms

public section

namespace Silmaril.SSA.PEG.Semantics.Proofs

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}
variable {g : Graph P params results n l}

private theorem appendWalk {V K : Type} {edge : V → K → V → Prop}
    {a b c : V} {p q : List K} (h : Walk edge a p b) (h' : Walk edge b q c) :
    Walk edge a (p ++ q) c := by
  induction h with
  | nil _ => exact h'
  | cons step _ ih => exact .cons step (ih h')

private theorem enclosing_wf {forest : LoopForest l} (h : forest.WellFormed) :
    WellFounded forest.StrictlyEncloses := by
  let _ : Finite (Fin l) := ⟨Equiv.refl _⟩
  let _ : Std.Irrefl forest.StrictlyEncloses := ⟨h⟩
  let _ : IsTrans (Fin l) forest.StrictlyEncloses := ⟨fun _ _ _ hab hbc => by
    obtain ⟨p, hp, pos⟩ := hbc
    obtain ⟨q, hq, _⟩ := hab
    exact ⟨p ++ q, appendWalk hp hq, fun empty => pos (List.append_eq_nil_iff.mp empty).1⟩⟩
  exact Finite.wellFounded_of_trans_of_irrefl _

/-- All sufficiently late keys among a finite set recur arbitrarily late. -/
private def Recurs {K : Type} (keys : Nat → K) (k : K) : Prop :=
  ∀ start, ∃ j ≥ start, keys j = k

private theorem recurrence_tail {K : Type} (keys : Nat → K) (keysList : List K) :
    ∃ start, ∀ j ≥ start, keys j ∈ keysList → Recurs keys (keys j) := by
  classical
  induction keysList with
  | nil => exact ⟨0, fun _ _ h => (List.not_mem_nil h).elim⟩
  | cons k ks ih =>
    obtain ⟨start, later⟩ := ih
    by_cases recur : Recurs keys k
    · refine ⟨start, fun j bound mem => ?_⟩
      rcases List.mem_cons.mp mem with isK | tail
      · exact isK.symm ▸ recur
      · exact later j bound tail
    · have stop : ∃ endAt, ∀ j ≥ endAt, keys j ≠ k := by
        simpa only [Recurs, not_forall, not_exists, not_and] using recur
      obtain ⟨endAt, stops⟩ := stop
      refine ⟨max endAt start, fun j bound mem => ?_⟩
      rcases List.mem_cons.mp mem with isK | tail
      · exact (stops j (Nat.le_trans (Nat.le_max_left _ _) bound) isK).elim
      · exact later j (Nat.le_trans (Nat.le_max_right _ _) bound) tail

private def allKinds (l : Nat) : List (EdgeKind (Fin l)) :=
  .ordinary :: (List.finRange l).flatMap fun loop =>
    [.initial loop, .feedback loop, .sample loop, .index loop]

private theorem mem_allKinds (kind : EdgeKind (Fin l)) : kind ∈ allKinds l := by
  cases kind with
  | ordinary => exact List.mem_cons_self
  | initial k | feedback k | sample k | index k =>
    exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨k, List.mem_finRange k, by simp⟩)

/-- The walk from request `start` for `len` transitions. -/
private def segment (kinds : Nat → EdgeKind (Fin l)) (start : Nat) : Nat → List (EdgeKind (Fin l))
  | 0 => []
  | len + 1 => kinds start :: segment kinds (start + 1) len

private theorem segment_walk (nodes : Nat → Fin n) (kinds : Nat → EdgeKind (Fin l))
    (step : ∀ j, g.Edge (nodes j) (kinds j) (nodes (j + 1))) (start len : Nat) :
    Walk g.Edge (nodes start) (segment kinds start len) (nodes (start + len)) := by
  induction len generalizing start with
  | zero => exact .nil _
  | succ len ih =>
    simp only [segment]
    rw [show start + (len + 1) = (start + 1) + len by omega]
    exact .cons (step start) (ih (start + 1))

private theorem segment_at {kinds : Nat → EdgeKind (Fin l)} {kind : EdgeKind (Fin l)}
    {start len : Nat} (mem : kind ∈ segment kinds start len) : ∃ j ≥ start, kinds j = kind := by
  induction len generalizing start with
  | zero => exact (List.not_mem_nil mem).elim
  | succ len ih =>
    rcases List.mem_cons.mp mem with first | tail
    · exact ⟨start, Nat.le_refl _, first.symm⟩
    · obtain ⟨j, bound, eq⟩ := ih tail
      exact ⟨j, by omega, eq⟩

private theorem segment_cycle (nodes : Nat → Fin n) (kinds : Nat → EdgeKind (Fin l))
    (step : ∀ j, g.Edge (nodes j) (kinds j) (nodes (j + 1))) {i j : Nat}
    (gt : i < j) (eq : nodes i = nodes j) :
    ∃ ks, Walk g.Edge (nodes i) ks (nodes i) ∧ kinds i ∈ ks ∧
      ∀ kind ∈ ks, ∃ t ≥ i, kinds t = kind := by
  let len := j - i
  have lenEq : i + len = j := by dsimp [len]; omega
  have pos : len ≠ 0 := by dsimp [len]; omega
  refine ⟨segment kinds i len, ?_, ?_, fun _ mem => segment_at mem⟩
  · simpa only [lenEq, ← eq] using segment_walk nodes kinds step i len
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero pos
    rw [hk]
    exact List.mem_cons_self

private theorem count_le {kind : EdgeKind (Fin l)} {i j : Index l}
    (h : kind.Changes i j) (loop : Fin l) (safe : kind ≠ .sample loop) : j loop ≤ i loop := by
  cases kind with
  | ordinary | index _ => obtain rfl := h; exact Nat.le_refl _
  | initial _ => obtain ⟨_, rfl⟩ := h; exact Nat.le_refl _
  | sample k =>
    obtain ⟨_, rfl⟩ := h
    have ne : loop ≠ k := fun eq => safe (eq ▸ rfl)
    simp [Index.set, ne]
  | feedback k =>
    obtain ⟨count, before, rfl⟩ := h
    by_cases same : loop = k
    · subst loop
      simp [Index.set, before]
    · simp [Index.set, same]

private theorem count_lt {i j : Index l} (loop : Fin l)
    (h : (EdgeKind.feedback loop).Changes i j) : j loop < i loop := by
  obtain ⟨count, before, rfl⟩ := h
  simp [Index.set, before]

/-- A coordinate with no late samples cannot have arbitrarily late feedback. -/
private theorem no_reset_no_recurrent_feedback (req : Nat → Request n l)
    (kind : Nat → EdgeKind (Fin l)) (change : ∀ j, (kind j).Changes (req j).2 (req (j + 1)).2)
    (start : Nat) (loop : Fin l) (noReset : ∀ j ≥ start, kind j ≠ .sample loop) :
    ¬Recurs kind (.feedback loop) := by
  classical
  intro recurrent
  let hit (count : Nat) := ∃ j ≥ start, (req j).2 loop = count
  have existsHit : ∃ count, hit count := ⟨_, start, Nat.le_refl _, rfl⟩
  obtain ⟨i, hi, minEq⟩ := Nat.find_spec existsHit
  obtain ⟨j, hj, feedback⟩ := recurrent i
  have after : ∀ j ≥ i, (req j).2 loop ≤ (req i).2 loop := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact Nat.le_refl _
    | succ t ht ih =>
      exact Nat.le_trans (count_le (change t) loop (noReset t (Nat.le_trans hi ht))) ih
  have lower : (req (j + 1)).2 loop < Nat.find existsHit := by
    have h := change j
    rw [feedback] at h
    exact Nat.lt_of_lt_of_le (count_lt loop h) (minEq ▸ after j hj)
  exact Nat.find_min existsHit lower ⟨j + 1, by omega, rfl⟩

/-- A hypothetical infinite demand walk must have a recurrent feedback loop.
Choose one minimal under ancestry. A recurrent sample of that loop would
force earlier feedback in an enclosing loop, while without any such sample
the counter cannot decrease indefinitely. -/
theorem demand_wf_of_cycles (forest : g.forest.WellFormed) (feedback : g.FeedbackCycles)
    (outerFeedback : g.OuterFeedbackCycles) : WellFounded g.Demand := by
  classical
  rw [wellFounded_iff_isEmpty_descending_chain]
  refine ⟨?_⟩
  rintro ⟨req, chain⟩
  let kind (j : Nat) := Classical.choose (chain j)
  have step (j : Nat) : g.Edge (req j).1 (kind j) (req (j + 1)).1 :=
    (Classical.choose_spec (chain j)).1
  have changes (j : Nat) : (kind j).Changes (req j).2 (req (j + 1)).2 :=
    (Classical.choose_spec (chain j)).2
  let keys j := ((req j).1, kind j)
  let keyList := (List.finRange n).flatMap fun a => (allKinds l).map fun k => (a, k)
  have keyMem (j : Nat) : keys j ∈ keyList :=
    List.mem_flatMap.mpr ⟨_, List.mem_finRange _, List.mem_map.mpr ⟨_, mem_allKinds _, rfl⟩⟩
  obtain ⟨start, tail⟩ := recurrence_tail keys keyList
  have recurs (j : Nat) (late : start ≤ j) : Recurs kind (kind j) := by
    intro s
    obtain ⟨t, ht, eq⟩ := tail j late (keyMem j) s
    exact ⟨t, ht, congrArg Prod.snd eq⟩
  have cycle (i : Nat) (late : start ≤ i) :
      ∃ ks, Walk g.Edge (req i).1 ks (req i).1 ∧ kind i ∈ ks ∧
        ∀ k ∈ ks, Recurs kind k := by
    obtain ⟨j, later, eq⟩ := tail i late (keyMem i) (i + 1)
    obtain ⟨ks, path, mem, memberAt⟩ := segment_cycle (fun j => (req j).1) kind step
      (show i < j from later) (congrArg (fun p : Fin n × EdgeKind (Fin l) => p.1) eq.symm)
    refine ⟨ks, path, mem, fun k hk => ?_⟩
    obtain ⟨t, ht, isK⟩ := memberAt k hk
    exact isK ▸ recurs t (Nat.le_trans late ht)
  have noneRecur (loop : Fin l) : ¬Recurs kind (.feedback loop) := by
    induction loop using (enclosing_wf forest).induction with
    | h loop ih =>
      apply no_reset_no_recurrent_feedback req kind changes start loop
      intro j hj sample
      obtain ⟨ks, path, mem, often⟩ := cycle j hj
      obtain ⟨outer, enclosed, visited⟩ :=
        outerFeedback _ ks path (kind j) mem loop (.inl sample)
      exact ih outer enclosed (often _ visited)
  obtain ⟨ks, path, mem, often⟩ := cycle start (Nat.le_refl _)
  obtain ⟨k, hk, found⟩ := feedback _ ks path (fun empty => by simp [empty] at mem)
  cases k <;> simp only [EdgeKind.IsFeedback] at found
  case feedback loop => exact noneRecur loop (often _ hk)

end Silmaril.SSA.PEG.Semantics.Proofs
