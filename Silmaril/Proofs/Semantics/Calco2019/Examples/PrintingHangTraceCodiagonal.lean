module

public import Silmaril.Semantics.Calco2019.Examples.Printing.HangTraces.Laws.Defs
import Silmaril.Proofs.Semantics.Calco2019.Examples.PrintingHangTraces

public section

universe u

namespace Silmaril.Calco2019.Examples.Printing.HangTraces.CodiagonalProofs

open Hangs

variable {A X Y : Type u}

variable (f : X → Traces A ((Y ⊕ X) ⊕ X))

private theorem flat_mem (x : X) (t : Model A (Y ⊕ X)) :
    t ∈ (Elgot.flattenBody f x).1 ↔ ∃ s ∈ (f x).1,
      (match s with
      | .inl (w, r) => Sum.inl (w, Elgot.flatten r)
      | .inr seq => Sum.inr seq) = t := by
  change (∃ s ∈ (f x).1, t ∈ extendSet (fun r => {Sum.inl ([], Elgot.flatten r)}) s) ↔ _
  apply exists_congr
  intro s
  apply and_congr_right'
  rcases s with ⟨w, r⟩ | seq
  · change (∃ a : Model A (Y ⊕ X), a = Sum.inl ([], Elgot.flatten r) ∧
        prependWord w a = t) ↔ _
    rw [exists_eq_left]
    change (Sum.inl (w ++ [], Elgot.flatten r) : Model A (Y ⊕ X)) = t ↔ _
    rw [List.append_nil]
  · exact eq_comm

private theorem return_mem (x : X) (w : List A) (y : Y) :
    Sum.inl (w, Sum.inl y) ∈ (Elgot.flattenBody f x).1 ↔
      Sum.inl (w, Sum.inl (Sum.inl y)) ∈ (f x).1 := by
  constructor
  · intro h
    obtain ⟨s, hs, eq⟩ := (flat_mem f x _).1 h
    rcases s with ⟨v, (y' | z) | z⟩ | seq <;> cases eq
    exact hs
  · intro h
    exact (flat_mem f x _).2 ⟨_, h, rfl⟩

private theorem stop_mem (x : X) (s : Stream'.Seq A) :
    Sum.inr s ∈ (Elgot.flattenBody f x).1 ↔ Sum.inr s ∈ (f x).1 := by
  constructor
  · intro h
    obtain ⟨t, ht, eq⟩ := (flat_mem f x _).1 h
    rcases t with ⟨w, r⟩ | seq <;> cases eq
    exact ht
  · intro h
    exact (flat_mem f x _).2 ⟨_, h, rfl⟩

private theorem step_mem (x z : X) (w : List A) :
    Sum.inl (w, Sum.inr z) ∈ (Elgot.flattenBody f x).1 ↔
      Sum.inl (w, Sum.inr z) ∈ (f x).1 ∨ Sum.inl (w, Sum.inl (Sum.inr z)) ∈ (f x).1 := by
  constructor
  · intro h
    obtain ⟨s, hs, eq⟩ := (flat_mem f x _).1 h
    rcases s with ⟨v, (y | z') | z'⟩ | seq <;> cases eq
    · exact .inr hs
    · exact .inl hs
  · rintro (h | h)
    · exact (flat_mem f x _).2 ⟨_, h, rfl⟩
    · exact (flat_mem f x _).2 ⟨_, h, rfl⟩

private theorem inner_step (x z : X) (w : List A) (t : Model A Y)
    (h : Sum.inl (w, Sum.inr z) ∈ (f x).1)
    (ht : Runs (iterate f) z t) : Runs (iterate f) x (prependWord w t) := by
  classical
  have eq := congrFun (iterate_fixpoint (iterate f)) x
  have law (a : X) : (iterate f a).1 = bindSet (f a).1
      (fun s => ((Sum.elim pure (iterate f)) s).1) :=
    congrArg Subtype.val (congrFun (iterate_fixpoint f) a)
  change prependWord w t ∈ (iterate (iterate f) x).1
  have leftAssoc (s : Model A (Y ⊕ X)) (hs : s ∈ (iterate f z).1)
      (hpost : t ∈ extendSet (fun r => ((Sum.elim pure (iterate (iterate f))) r).1) s) :
      prependWord w t ∈ (iterate (iterate f) x).1 := by
    rw [eq]
    refine ⟨prependWord w s, ?_, ?_⟩
    · rw [law x]
      exact ⟨_, h, _, hs, rfl⟩
    · rcases s with ⟨v, y | x'⟩ | seq
      · obtain ⟨u, hu, rfl⟩ := hpost
        exact ⟨u, hu, (prependWord_append w v u).symm⟩
      · obtain ⟨u, hu, rfl⟩ := hpost
        exact ⟨u, hu, (prependWord_append w v u).symm⟩
      · have e : t = Sum.inr seq := hpost
        subst t
        rfl
  change t ∈ (iterate (iterate f) z).1 at ht
  rw [congrFun (iterate_fixpoint (iterate f)) z] at ht
  obtain ⟨s, hs, ht⟩ := ht
  exact leftAssoc s hs ht

private theorem outer_step (x z : X) (w : List A) (t : Model A Y)
    (h : Sum.inl (w, Sum.inl (Sum.inr z)) ∈ (f x).1)
    (ht : Runs (iterate f) z t) : Runs (iterate f) x (prependWord w t) := by
  change prependWord w t ∈ (iterate (iterate f) x).1
  rw [congrFun (iterate_fixpoint (iterate f)) x]
  exact ⟨Sum.inl (w, Sum.inr z), Or.inl (.ret h), t, ht, rfl⟩

theorem finite_flat_to_nested {x : X} {t : Model A Y}
    (h : FiniteRun (Elgot.flattenBody f) x t) : Runs (iterate f) x t := by
  induction h with
  | ret h =>
    exact .inl (.ret (.inl (.ret ((return_mem f _ _ _).1 h))))
  | stop h =>
    exact .inl (.stop (.inl (.stop ((stop_mem f _ _).1 h))))
  | step h _ ih =>
    rcases (step_mem f _ _ _).1 h with h | h
    · exact inner_step f _ _ _ _ h ih
    · exact outer_step f _ _ _ _ h ih

private theorem flat_step {x z : X} {w : List A} {t : Model A Y}
    (h : Sum.inl (w, Sum.inr z) ∈ (Elgot.flattenBody f x).1)
    (ht : Runs (Elgot.flattenBody f) z t) :
    Runs (Elgot.flattenBody f) x (prependWord w t) := by
  change prependWord w t ∈ (iterate (Elgot.flattenBody f) x).1
  rw [congrFun (iterate_fixpoint (Elgot.flattenBody f)) x]
  exact ⟨_, h, t, ht, rfl⟩

private theorem lift_inner_finite {x : X} {t : Model A (Y ⊕ X)}
    (h : FiniteRun f x t) :
    (∀ y w, t = .inl (w, .inl y) → Runs (Elgot.flattenBody f) x (.inl (w, y))) ∧
    (∀ s, t = .inr s → Runs (Elgot.flattenBody f) x (.inr s)) ∧
    (∀ z w u, t = .inl (w, .inr z) → Runs (Elgot.flattenBody f) z u →
      Runs (Elgot.flattenBody f) x (prependWord w u)) := by
  induction h with
  | ret h =>
    refine ⟨?_, ?_, ?_⟩
    · intro y w eq
      cases eq
      exact .inl (.ret ((return_mem f _ _ _).2 h))
    · intro s eq
      cases eq
    · intro z w u eq run
      cases eq
      exact flat_step f ((step_mem f _ _ _).2 (.inr h)) run
  | stop h =>
    refine ⟨?_, ?_, ?_⟩
    · intro y w eq
      cases eq
    · intro s eq
      cases eq
      exact .inl (.stop ((stop_mem f _ _).2 h))
    · intro z w u eq
      cases eq
  | @step x z w t h _ ih =>
    have edge := (step_mem f x z w).2 (.inl h)
    rcases t with ⟨v, y | z'⟩ | seq
    · refine ⟨?_, ?_, ?_⟩
      · intro y' word eq
        change (Sum.inl (w ++ v, Sum.inl y) : Model A (Y ⊕ X)) = _ at eq
        cases eq
        exact flat_step f edge (ih.1 _ _ rfl)
      · intro s eq
        cases eq
      · intro z' word u eq
        change (Sum.inl (w ++ v, Sum.inl y) : Model A (Y ⊕ X)) = _ at eq
        cases eq
    · refine ⟨?_, ?_, ?_⟩
      · intro y word eq
        change (Sum.inl (w ++ v, Sum.inr z') : Model A (Y ⊕ X)) = _ at eq
        cases eq
      · intro s eq
        cases eq
      · intro z'' word u eq hu
        change (Sum.inl (w ++ v, Sum.inr z') : Model A (Y ⊕ X)) = _ at eq
        cases eq
        rw [← prependWord_append]
        exact flat_step f edge (ih.2.2 _ _ _ rfl hu)
    · refine ⟨?_, ?_, ?_⟩
      · intro y word eq
        cases eq
      · intro s eq
        cases eq
        exact flat_step f edge (ih.2.1 _ rfl)
      · intro z' word u eq
        cases eq

theorem finite_nested_to_flat {x : X} {t : Model A Y}
    (h : FiniteRun (iterate f) x t) : Runs (Elgot.flattenBody f) x t := by
  induction h with
  | ret h =>
    change Runs f _ (.inl (_, .inl _)) at h
    rcases h with h | ⟨p, seq, eq, _⟩
    · exact (lift_inner_finite f h).1 _ _ rfl
    · cases eq
  | stop h =>
    change Runs f _ (.inr _) at h
    rcases h with h | ⟨p, hp⟩
    · exact (lift_inner_finite f h).2.1 _ rfl
    · let q : InfiniteRun (Elgot.flattenBody f) _ := {
        state := p.state
        word := p.word
        start := p.start
        edge := fun i => (step_mem f _ _ _).2 (.inl (p.edge i)) }
      obtain ⟨s, eq, obs⟩ := hp
      exact .inr ⟨q, s, congrArg Sum.inr (Sum.inr.inj eq), obs⟩
  | step h _ ih =>
    change Runs f _ (.inl (_, .inr _)) at h
    rcases h with h | ⟨p, seq, eq, _⟩
    · exact (lift_inner_finite f h).2.2 _ _ _ rfl ih
    · cases eq

private def interval (w : ℕ → List A) (start len : ℕ) : List A :=
  (List.ofFn fun i : Fin len => w (start + i)).flatten

private theorem interval_succ (w : ℕ → List A) (start len : ℕ) :
    interval w start (len + 1) = w start ++ interval w (start + 1) len := by
  simp only [interval, List.ofFn_succ, List.flatten_cons, Fin.val_zero, Nat.add_zero,
    Fin.val_succ]
  congr 3
  funext i
  congr 1
  omega

private theorem interval_add (w : ℕ → List A) (start n m : ℕ) :
    interval w start (n + m) = interval w start n ++ interval w (start + n) m := by
  simp only [interval, List.ofFn_add, List.flatten_append, Fin.val_castLE, Fin.val_natAdd,
    Nat.add_assoc]

private theorem interval_prefix (w : ℕ → List A) (n : ℕ) :
    interval w 0 n = wordsPrefix w n := by
  have eq (start len : ℕ) :
      interval w start len = wordsPrefix (fun i => w (start + i)) len := by
    induction len generalizing start with
    | zero => rfl
    | succ n ih =>
      rw [interval_succ, ih, wordsPrefix]
      simp only [Nat.add_zero]
      congr 2
      funext i
      congr 1
      omega
  simpa only [Nat.zero_add] using eq 0 n

private theorem chunkAt_cofinal (w v : ℕ → List A)
    (hw : ∀ n, ∃ m, wordsPrefix w n <+: wordsPrefix v m)
    (hv : ∀ n, ∃ m, wordsPrefix v n <+: wordsPrefix w m) (i : ℕ) :
    chunkAt w i = chunkAt v i := by
  apply Option.ext
  intro a
  rw [chunkAt_some, chunkAt_some]
  have forward (u v : ℕ → List A) (h : ∀ n, ∃ m, wordsPrefix u n <+: wordsPrefix v m)
      (hu : LetterAt u i a) : LetterAt v i a := by
    obtain ⟨n, hn⟩ := hu
    obtain ⟨m, extra, eq⟩ := h n
    have hi := (List.getElem?_eq_some_iff.mp hn).choose
    exact ⟨m, by rw [← eq, List.getElem?_append_left hi, hn]⟩
  exact ⟨forward w v hw, forward v w hv⟩

private theorem chunkAt_grouped (w : ℕ → List A) (cuts : ℕ → ℕ)
    (first : cuts 0 = 0) (strict : StrictMono cuts) (n : ℕ) :
    chunkAt (fun i => interval w (cuts i) (cuts (i+1) - cuts i)) n = chunkAt w n := by
  have groups (base rounds : ℕ) :
      wordsPrefix (fun i => interval w (cuts (base + i)) (cuts (base + i + 1) - cuts (base + i))) rounds =
        interval w (cuts base) (cuts (base + rounds) - cuts base) := by
    induction rounds generalizing base with
    | zero => simp [wordsPrefix, interval]
    | succ rounds ih =>
      have h1 := strict.monotone (show base ≤ base + 1 by omega)
      have h2 := strict.monotone (show base + 1 ≤ base + 1 + rounds by omega)
      rw [wordsPrefix]
      simp only [Nat.add_zero]
      rw [show (fun i => interval w (cuts (base + (i + 1)))
            (cuts (base + (i + 1) + 1) - cuts (base + (i + 1)))) =
          (fun i => interval w (cuts (base + 1 + i))
            (cuts (base + 1 + i + 1) - cuts (base + 1 + i))) by
          funext i; rw [show base + (i + 1) = base + 1 + i by omega]]
      rw [ih, show base + (rounds + 1) = base + 1 + rounds by omega]
      rw [show cuts (base + 1 + rounds) - cuts base =
        (cuts (base + 1) - cuts base) + (cuts (base + 1 + rounds) - cuts (base + 1)) by omega,
        interval_add, show cuts base + (cuts (base + 1) - cuts base) = cuts (base + 1) by omega]
  have prefixEq (k : ℕ) : wordsPrefix (fun i => interval w (cuts i) (cuts (i+1) - cuts i)) k =
      wordsPrefix w (cuts k) := by
    have eq := groups 0 k
    simp only [Nat.zero_add, first, Nat.sub_zero] at eq
    exact eq.trans (interval_prefix w _)
  apply chunkAt_cofinal
  · intro k
    exact ⟨cuts k, [], by rw [prefixEq, List.append_nil]⟩
  · intro k
    refine ⟨k, ?_⟩
    rw [prefixEq]
    have le : k ≤ cuts k := strict.id_le k
    rw [← interval_prefix, ← interval_prefix]
    have eq : cuts k = k + (cuts k - k) := by omega
    conv_rhs => rw [eq, interval_add]
    exact List.prefix_append _ _

private def IsOuter {x : X} (p : InfiniteRun (Elgot.flattenBody f) x) (n : ℕ) : Prop :=
  Sum.inl (p.word n, Sum.inl (Sum.inr (p.state (n+1)))) ∈ (f (p.state n)).1

private theorem has_inner {x : X} (p : InfiniteRun (Elgot.flattenBody f) x) (n : ℕ)
    (h : ¬IsOuter f p n) :
    Sum.inl (p.word n, Sum.inr (p.state (n+1))) ∈ (f (p.state n)).1 :=
  ((step_mem f _ _ _).1 (p.edge n)).resolve_right h

private theorem inner_segment {x : X} (p : InfiniteRun (Elgot.flattenBody f) x)
    (start len : ℕ) (internal : ∀ i, start ≤ i → i < start + len → ¬IsOuter f p i)
    (last : IsOuter f p (start + len)) :
    FiniteRun f (p.state start)
      (.inl (interval p.word start (len + 1), .inr (p.state (start + len + 1)))) := by
  induction len generalizing start with
  | zero =>
    have eq : interval p.word start 1 = p.word start := by
      rw [interval_succ]
      simp [interval]
    rw [eq, Nat.add_zero]
    exact .ret last
  | succ len ih =>
    have rest := ih (start + 1) (fun i hlo hhi =>
      internal i (by omega) (by omega)) (by
        rw [show start + 1 + len = start + (len + 1) by omega]
        exact last)
    rw [interval_succ]
    rw [show start + (len + 1) + 1 = start + 1 + len + 1 by omega]
    exact .step (has_inner f p start (internal start le_rfl (by omega))) rest

private theorem nested_forever_many {x : X} (p : InfiniteRun (Elgot.flattenBody f) x)
    (h : ∀ i, ∃ j, i ≤ j ∧ IsOuter f p j) (t : Model A Y) (ht : p.realizes t) :
    Runs (iterate f) x t := by
  classical
  -- Pick the first outer step so each preceding edge can run internally.
  let first : (i : ℕ) → ℕ := fun i => Nat.find (h i)
  let cuts : ℕ → ℕ := Nat.rec 0 (fun _ i => first i + 1)
  have step (i : ℕ) : cuts (i + 1) = first (cuts i) + 1 := rfl
  have firstSpec (i : ℕ) : i ≤ first i ∧ IsOuter f p (first i) := Nat.find_spec (h i)
  have bound (i : ℕ) : cuts i < cuts (i + 1) :=
    step i ▸ Nat.lt_succ_of_le (firstSpec (cuts i)).1
  let q : InfiniteRun (iterate f) x := {
    state := fun i => p.state (cuts i)
    word := fun i => interval p.word (cuts i) (cuts (i+1) - cuts i)
    start := p.start
    edge := fun i => by
      change Runs f (p.state (cuts i))
        (.inl (interval p.word (cuts i) (cuts (i+1) - cuts i), .inr (p.state (cuts (i+1)))))
      let len := first (cuts i) - cuts i
      have eq : cuts i + len = first (cuts i) := Nat.add_sub_of_le (firstSpec (cuts i)).1
      have n : len + 1 = cuts (i + 1) - cuts i := by rw [step]; omega
      have target : cuts i + len + 1 = cuts (i + 1) := by rw [step, eq]
      rw [← n, ← target]
      exact .inl (inner_segment f p _ _ (fun j hmin hmax hj =>
        (Nat.find_min (h (cuts i)) (show j < first (cuts i) from eq ▸ hmax)) ⟨hmin, hj⟩) (eq.symm ▸ (firstSpec (cuts i)).2)) }
  refine .inr ⟨q, ?_⟩
  obtain ⟨s, eq, obs⟩ := ht
  exact ⟨s, eq, fun n => (obs n).trans (chunkAt_grouped p.word cuts rfl
    (strictMono_nat_of_lt_succ bound) n).symm⟩

private theorem nested_forever_tail {x : X} (p : InfiniteRun (Elgot.flattenBody f) x)
    (i : ℕ) (h : ∀ j, i ≤ j → ¬IsOuter f p j) :
    Runs (iterate f) (p.state i) (.inr (Proofs.chunks (fun j => p.word (i+j)))) := by
  let q : InfiniteRun f (p.state i) :=
    ⟨fun j => p.state (i+j), fun j => p.word (i+j), by simp,
      fun j => by simpa only [Nat.add_assoc] using has_inner f p (i+j) (h _ (Nat.le_add_right _ _))⟩
  exact .inl (.stop (.inr ⟨q, (Proofs.realizes_eq _ _).2 rfl⟩))

private theorem nested_forever_few {x : X} (p : InfiniteRun (Elgot.flattenBody f) x)
    (N : ℕ) (h : ∀ j, N ≤ j → ¬IsOuter f p j) (t : Model A Y) (ht : p.realizes t) :
    Runs (iterate f) x t := by
  have go (fuel : ℕ) : ∀ i, i + fuel = N →
      Runs (iterate f) (p.state i) (Sum.inr (Proofs.chunks (fun j => p.word (i+j)))) := by
    induction fuel with
    | zero =>
      intro i ei
      have e : i = N := by omega
      subst i
      exact nested_forever_tail f p N h
    | succ fuel ih =>
      intro i ei
      have tail := ih (i+1) (by omega)
      have chunks : (Sum.inr (Proofs.chunks (fun j => p.word (i+j))) : Model A Y) =
          prependWord (p.word i) (.inr (Proofs.chunks (fun j => p.word (i+1+j)))) := by
        apply congrArg Sum.inr
        have e := Proofs.chunks_step (fun j => p.word (i+j))
        simp only [Nat.add_zero] at e
        refine e.trans ?_
        congr 2
        funext j
        congr 1
        omega
      rw [chunks]
      rcases (step_mem f _ _ _).1 (p.edge i) with edge | edge
      · exact inner_step f _ _ _ _ edge tail
      · exact outer_step f _ _ _ _ edge tail
  rw [(Proofs.realizes_eq p t).1 ht]
  simpa only [Nat.zero_add, p.start] using go N 0 (Nat.zero_add N)

theorem infinite_flat_to_nested {x : X} (p : InfiniteRun (Elgot.flattenBody f) x)
    (t : Model A Y) (ht : p.realizes t) : Runs (iterate f) x t := by
  classical
  by_cases h : ∀ i, ∃ j, i ≤ j ∧ IsOuter f p j
  · exact nested_forever_many f p h t ht
  · push Not at h
    obtain ⟨N, h⟩ := h
    exact nested_forever_few f p N h t ht

private structure Block (x z : X) (w : List A) where
  len : ℕ
  positive : 0 < len
  state : ℕ → X
  word : ℕ → List A
  start : state 0 = x
  finish : state len = z
  edge (i : ℕ) : i < len →
    Sum.inl (word i, Sum.inr (state (i+1))) ∈ (Elgot.flattenBody f (state i)).1
  output : interval word 0 len = w

private theorem run_block {x : X} {r : Model A (Y ⊕ X)} (h : FiniteRun f x r) :
    ∀ (w : List A) (z : X), r = .inl (w, .inr z) → Nonempty (Block f x z w) := by
  induction h with
  | @ret x word result hr =>
    intro w z eq
    cases eq
    exact ⟨⟨1, by decide, Nat.rec x (fun _ _ => z), fun _ => word, rfl, rfl,
      fun i hi => by
        have hz : i = 0 := by omega
        subst i
        exact (step_mem f _ _ _).2 (.inr hr),
      by simp [interval, List.ofFn_succ]⟩⟩
  | stop h =>
    intro w z eq
    cases eq
  | @step x next word r edge _ ih =>
    intro w z eq
    rcases r with ⟨v, y | z'⟩ | seq
    · change (Sum.inl (word ++ v, Sum.inl y) : Model A (Y ⊕ X)) = _ at eq
      cases eq
    · change (Sum.inl (word ++ v, Sum.inr z') : Model A (Y ⊕ X)) = _ at eq
      cases eq
      obtain ⟨block⟩ := ih v z rfl
      let state : ℕ → X := fun
        | 0 => x
        | i + 1 => block.state i
      let letters : ℕ → List A := fun
        | 0 => word
        | i + 1 => block.word i
      refine ⟨⟨block.len + 1, by omega, state, letters, rfl, block.finish, ?_, ?_⟩⟩
      · intro i hi
        cases i with
        | zero =>
          change Sum.inl (word, Sum.inr (block.state 0)) ∈ (Elgot.flattenBody f x).1
          rw [block.start]
          exact (step_mem f _ _ _).2 (.inl edge)
        | succ i => exact block.edge i (by omega)
      · rw [interval_succ]
        change word ++ interval letters 1 block.len = word ++ v
        congr 1
        refine Eq.trans ?_ block.output
        unfold interval
        congr 2
        funext i
        rw [Nat.zero_add, Nat.add_comm 1]
    · cases eq

private theorem nested_run_block {x z : X} {w : List A}
    (h : Sum.inl (w, Sum.inr z) ∈ (iterate f x).1) : Nonempty (Block f x z w) := by
  change Runs f x (.inl (w, .inr z)) at h
  rcases h with h | ⟨p, s, eq, obs⟩
  · exact run_block f h w z rfl
  · cases eq

private theorem infinite_nested_to_flat {x : X} (p : InfiniteRun (iterate f) x)
    (t : Model A Y) (ht : p.realizes t) : Runs (Elgot.flattenBody f) x t := by
  classical
  let block (i : ℕ) : Block f (p.state i) (p.state (i+1)) (p.word i) :=
    Classical.choice (nested_run_block f (p.edge i))
  let cuts : ℕ → ℕ := Nat.rec 0 (fun i base => base + (block i).len)
  have next (i : ℕ) : cuts (i + 1) = cuts i + (block i).len := rfl
  have positive (i : ℕ) : cuts i < cuts (i + 1) := by
    rw [next]
    exact Nat.lt_add_of_pos_right (block i).positive
  have strict := strictMono_nat_of_lt_succ positive
  have upper (i : ℕ) : ∃ j, i < cuts (j + 1) :=
    ⟨i, Nat.lt_of_le_of_lt (strict.id_le i) (positive i)⟩
  let index (i : ℕ) := Nat.find (upper i)
  have index_of (i j : ℕ) (lo : cuts j ≤ i) (hi : i < cuts (j + 1)) : index i = j := by
    have le : index i ≤ j := Nat.find_min' (upper i) hi
    apply Nat.le_antisymm le
    apply Nat.le_of_not_gt
    intro lt
    have bound := strict.monotone (show index i + 1 ≤ j by omega)
    have reach : i < cuts (index i + 1) := Nat.find_spec (upper i)
    omega
  have bounds (i : ℕ) : cuts (index i) ≤ i ∧ i < cuts (index i + 1) := by
    refine ⟨?_, Nat.find_spec (upper i)⟩
    apply Nat.le_of_not_gt
    intro lt
    cases h : index i with
    | zero =>
      rw [h] at lt
      exact (Nat.not_lt_zero _) lt
    | succ j =>
      rw [h] at lt
      exact (Nat.find_min (upper i) (show j < index i by omega)) lt
  let state (i : ℕ) := (block (index i)).state (i - cuts (index i))
  let word (i : ℕ) := (block (index i)).word (i - cuts (index i))
  let q : InfiniteRun (Elgot.flattenBody f) x := {
    state := state
    word := word
    start := by
      have eq := index_of 0 0 (Nat.le_refl 0) (positive 0)
      change (block (index 0)).state (0 - cuts (index 0)) = x
      rw [eq]
      exact (block 0).start.trans p.start
    edge := fun i => by
      have hi := bounds i
      have e := (block (index i)).edge (i - cuts (index i)) (by
        have step := next (index i)
        omega)
      change Sum.inl (word i, Sum.inr (state (i+1))) ∈ (Elgot.flattenBody f (state i)).1
      have advance : state (i+1) = (block (index i)).state (i - cuts (index i) + 1) := by
        by_cases stay : i + 1 < cuts (index i + 1)
        · have eq := index_of (i+1) (index i) (by omega) stay
          change (block (index (i+1))).state (i+1 - cuts (index (i+1))) = _
          rw [eq, show i + 1 - cuts (index i) = i - cuts (index i) + 1 by omega]
        · have boundary : i + 1 = cuts (index i + 1) := by omega
          have eq := index_of (i+1) (index i+1) (by omega) (by rw [boundary]; exact positive (index i + 1))
          change (block (index (i+1))).state (i+1 - cuts (index (i+1))) = _
          rw [eq, show i + 1 - cuts (index i + 1) = 0 by omega]
          rw [show i - cuts (index i) + 1 = (block (index i)).len by
            have step := next (index i)
            omega]
          exact (block _).start.trans (block _).finish.symm
      rw [advance]
      exact e }
  have grouped (i : ℕ) : interval word (cuts i) (cuts (i+1) - cuts i) = p.word i := by
    rw [show cuts (i+1) - cuts i = (block i).len by rw [next]; omega]
    refine Eq.trans ?_ (block i).output
    unfold interval
    congr 2
    funext j
    change (block (index (cuts i + j))).word (cuts i + j - cuts (index (cuts i + j))) = _
    have eq := index_of (cuts i + j) i (by omega) (by
      rw [next]
      have hj := j.isLt
      omega)
    rw [eq]
    congr 1
    omega
  refine .inr ⟨q, ?_⟩
  obtain ⟨seq, eq, obs⟩ := ht
  refine ⟨seq, eq, fun n => (obs n).trans ?_⟩
  exact (congrArg (fun w => chunkAt w n) (funext grouped)).symm.trans
    (chunkAt_grouped word cuts rfl strict n)

theorem codiagonal : iterate (iterate f) = iterate (Elgot.flattenBody f) := by
  funext x
  apply Subtype.ext
  ext t
  change Runs (iterate f) x t ↔ Runs (Elgot.flattenBody f) x t
  exact ⟨fun h => h.elim (finite_nested_to_flat f) (fun ⟨p, hp⟩ => infinite_nested_to_flat f p t hp),
    fun h => h.elim (finite_flat_to_nested f) (fun ⟨p, hp⟩ => infinite_flat_to_nested f p t hp)⟩

end Silmaril.Calco2019.Examples.Printing.HangTraces.CodiagonalProofs
