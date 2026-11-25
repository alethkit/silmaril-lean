module

public import Silmaril.Semantics.Calco2019.Examples.Printing.HangTraces.Defs

public section

universe u

namespace Silmaril.Calco2019.Examples.Printing.HangTraces.Proofs

open Hangs

variable {A X Y Z : Type u}

attribute [local instance] seqAction

theorem prefix_nil (t : Model A X) : prependWord [] t = t := by
  rcases t with ⟨w, x⟩ | s
  · rfl
  · exact congrArg Sum.inr (Stream'.Seq.nil_append s)

theorem prefix_append (w v : List A) (t : Model A X) :
    prependWord w (prependWord v t) = prependWord (w ++ v) t := by
  rcases t with ⟨u, x⟩ | s
  · exact congrArg (fun w => Sum.inl (w, x)) (List.append_assoc w v u).symm
  · change Sum.inr ((Stream'.Seq.ofList w).append ((Stream'.Seq.ofList v).append s)) =
      Sum.inr ((Stream'.Seq.ofList (w ++ v)).append s)
    rw [Stream'.Seq.ofList_append, Stream'.Seq.append_assoc]

private theorem mem_bind {p : Set (Model A X)} {f : X → Set (Model A Y)} {t : Model A Y} :
    t ∈ bindSet p f ↔ ∃ s ∈ p, t ∈ extendSet f s := Iff.rfl

private theorem bind_single_hang (s : Stream'.Seq A) (g : Y → Set (Model A Z)) :
    bindSet ({.inr s} : Set (Model A Y)) g = {.inr s} := by
  ext t
  rw [mem_bind]
  simp only [Set.mem_singleton_iff, exists_eq_left, extendSet]

private theorem bind_prefix (w : List A) (p : Set (Model A Y)) (g : Y → Set (Model A Z)) :
    bindSet (prependWord w '' p) g = prependWord w '' bindSet p g := by
  ext r
  rw [mem_bind, Set.mem_image]
  constructor
  · rintro ⟨s, ⟨t, ht, rfl⟩, hr⟩
    rcases t with ⟨v, y⟩ | seq
    · obtain ⟨u, hu, eq⟩ := hr
      exact ⟨prependWord v u, ⟨.inl (v, y), ht, u, hu, rfl⟩,
        (prefix_append w v u).trans eq⟩
    · exact ⟨.inr seq, ⟨.inr seq, ht, rfl⟩, hr.symm⟩
  · rintro ⟨u, ⟨t, ht, hu⟩, rfl⟩
    refine ⟨prependWord w t, ⟨t, ht, rfl⟩, ?_⟩
    rcases t with ⟨v, y⟩ | seq
    · obtain ⟨v', hv, rfl⟩ := hu
      exact ⟨v', hv, (prefix_append w v v').symm⟩
    · have eq : u = Sum.inr seq := hu
      subst u
      rfl

private theorem bind_extend (f : X → Set (Model A Y)) (g : Y → Set (Model A Z)) (t : Model A X) :
    bindSet (extendSet f t) g = extendSet (fun x => bindSet (f x) g) t := by
  rcases t with ⟨w, x⟩ | seq
  · exact bind_prefix w (f x) g
  · exact bind_single_hang seq g

theorem lawful (A : Type u) : LawfulMonad (Traces A) := by
  refine LawfulMonad.mk' (m := Traces A) (bind_pure_comp := fun _ _ => rfl) ?_ ?_ ?_
  · intro X p
    apply Subtype.ext
    ext t
    change t ∈ bindSet p.1 (fun x => {Sum.inl ([], x)}) ↔ t ∈ p.1
    constructor
    · rintro ⟨s, hs, ht⟩
      rcases s with ⟨w, x⟩ | seq
      · obtain ⟨_, rfl, rfl⟩ := ht
        simpa [prependWord, WriterAction.prependOutput] using hs
      · exact (show t = Sum.inr seq from ht) ▸ hs
    · intro ht
      refine ⟨t, ht, ?_⟩
      rcases t with ⟨w, x⟩ | seq
      · exact ⟨.inl ([], x), rfl, congrArg (fun w => Sum.inl (w, x)) (List.append_nil w)⟩
      · rfl
  · intro X Y x f
    apply Subtype.ext
    ext t
    change t ∈ bindSet {Sum.inl ([], x)} (fun x => (f x).1) ↔ t ∈ (f x).1
    rw [mem_bind]
    simp only [Set.mem_singleton_iff, exists_eq_left, extendSet, Set.mem_image, prefix_nil, exists_eq_right]
  · intro X Y Z p f g
    apply Subtype.ext
    ext t
    change t ∈ bindSet (bindSet p.1 (fun x => (f x).1)) (fun y => (g y).1) ↔
      t ∈ bindSet p.1 (fun x => bindSet (f x).1 (fun y => (g y).1))
    simp only [mem_bind]
    constructor
    · rintro ⟨s, ⟨r, hr, hs⟩, ht⟩
      refine ⟨r, hr, ?_⟩
      rw [← bind_extend]
      exact ⟨s, hs, ht⟩
    · rintro ⟨r, hr, ht⟩
      rw [← bind_extend] at ht
      obtain ⟨s, hs, ht⟩ := ht
      exact ⟨s, ⟨r, hr, hs⟩, ht⟩

private theorem wordsPrefix_step (w : ℕ → List A) (n : ℕ) :
    wordsPrefix w n <+: wordsPrefix w (n + 1) := by
  induction n generalizing w with
  | zero => exact List.nil_prefix
  | succ n ih => exact (List.prefix_append_right_inj _).2 (ih _)

private theorem wordsPrefix_le (w : ℕ → List A) {m n : ℕ} (h : m ≤ n) :
    wordsPrefix w m <+: wordsPrefix w n := by
  induction h with
  | refl => exact ⟨[], List.append_nil _⟩
  | step h ih => exact ih.trans (wordsPrefix_step w _)

private theorem letter_unique (w : ℕ → List A) {n : ℕ} {a b : A}
    (ha : LetterAt w n a) (hb : LetterAt w n b) : a = b := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  have same {i j : ℕ} {a b : A} (h : i ≤ j)
      (hi : (wordsPrefix w i)[n]? = some a) (hj : (wordsPrefix w j)[n]? = some b) : a = b := by
    obtain ⟨extra, he⟩ := wordsPrefix_le w h
    have hn := (List.getElem?_eq_some_iff.mp hi).choose
    rw [← he, List.getElem?_append_left hn, hi] at hj
    exact Option.some.inj hj
  rcases le_total i j with h | h
  · exact same h hi hj
  · exact (same h hj hi).symm

theorem chunkAt_some (w : ℕ → List A) (n : ℕ) (a : A) :
    chunkAt w n = some a ↔ LetterAt w n a := by
  classical
  unfold chunkAt
  split
  · rename_i h
    exact ⟨fun eq => Option.some.inj eq ▸ h.choose_spec,
      fun ha => congrArg some (letter_unique w h.choose_spec ha)⟩
  · exact ⟨fun h => by contradiction, fun h => False.elim ((by assumption : ¬ ∃ a, LetterAt w n a) ⟨a, h⟩)⟩

theorem chunkAt_isSeq (w : ℕ → List A) : Stream'.IsSeq (chunkAt w) := by
  intro n h
  cases eq : chunkAt w (n + 1) with
  | none => rfl
  | some a =>
    obtain ⟨k, hk⟩ := (chunkAt_some w _ _).mp eq
    have hn : n < (wordsPrefix w k).length := by
      have := (List.getElem?_eq_some_iff.mp hk).choose
      omega
    have prev := (chunkAt_some w n _).2 ⟨k, List.getElem?_eq_getElem hn⟩
    rw [h] at prev
    contradiction

private theorem letterAt_head (w : ℕ → List A) (n : ℕ) (a : A) :
    LetterAt w n a ↔ if n < (w 0).length then (w 0)[n]? = some a
      else LetterAt (fun i => w (i + 1)) (n - (w 0).length) a := by
  by_cases h : n < (w 0).length
  · rw [ite_eq_left h]
    constructor
    · rintro ⟨i, hi⟩
      cases i with
      | zero => contradiction
      | succ i =>
        rw [wordsPrefix, List.getElem?_append_left h] at hi
        exact hi
    · intro e
      exact ⟨1, by simpa [wordsPrefix] using e⟩
  · rw [ite_eq_right h]
    have hn := Nat.le_of_not_gt h
    constructor
    · rintro ⟨i, hi⟩
      cases i with
      | zero => contradiction
      | succ i =>
        rw [wordsPrefix, List.getElem?_append_right hn] at hi
        exact ⟨i, hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨i + 1, by rwa [wordsPrefix, List.getElem?_append_right hn]⟩

private theorem append_get (w : List A) (s : Stream'.Seq A) (n : ℕ) :
    ((Stream'.Seq.ofList w).append s).get? n =
      if n < w.length then w[n]? else s.get? (n - w.length) := by
  induction w generalizing n with
  | nil => simp
  | cons a w ih =>
    rw [Stream'.Seq.ofList_cons, Stream'.Seq.cons_append]
    cases n with
    | zero => simp
    | succ n =>
      rw [Stream'.Seq.get?_cons_succ, ih]
      simp

theorem chunk_head (w : ℕ → List A) :
    (⟨chunkAt w, chunkAt_isSeq w⟩ : Stream'.Seq A) =
      (Stream'.Seq.ofList (w 0)).append ⟨chunkAt (fun i => w (i + 1)), chunkAt_isSeq _⟩ := by
  apply Stream'.Seq.ext
  intro n
  let tail : Stream'.Seq A := ⟨chunkAt (fun i => w (i + 1)), chunkAt_isSeq _⟩
  change chunkAt w n = ((Stream'.Seq.ofList (w 0)).append tail).get? n
  rw [append_get]
  apply Option.ext
  intro a
  rw [chunkAt_some, letterAt_head]
  split
  · rfl
  · exact (chunkAt_some _ _ _).symm

noncomputable def chunks (w : ℕ → List A) : Stream'.Seq A :=
  ⟨chunkAt w, chunkAt_isSeq w⟩

theorem realizes_eq {f : X → Traces A (Y ⊕ X)} {x : X} (p : InfiniteRun f x) (t : Model A Y) :
    p.realizes t ↔ t = .inr (chunks p.word) := by
  constructor
  · rintro ⟨s, rfl, h⟩
    exact congrArg Sum.inr (Stream'.Seq.ext h)
  · rintro rfl
    exact ⟨chunks p.word, rfl, fun _ => rfl⟩

private def tailRun {f : X → Traces A (Y ⊕ X)} {x : X} (p : InfiniteRun f x) :
    InfiniteRun f (p.state 1) where
  state i := p.state (i + 1)
  word i := p.word (i + 1)
  start := rfl
  edge i := p.edge (i + 1)

private def consRun {f : X → Traces A (Y ⊕ X)} {x z : X} {w : List A}
    (h : .inl (w, .inr z) ∈ (f x).1) (p : InfiniteRun f z) : InfiniteRun f x where
  state
    | 0 => x
    | i + 1 => p.state i
  word
    | 0 => w
    | i + 1 => p.word i
  start := rfl
  edge
    | 0 => by simpa only [p.start] using h
    | i + 1 => p.edge i

theorem runs_nonempty (f : X → Traces A (Y ⊕ X)) (x : X) :
    ∃ t, Runs f x t := by
  classical
  by_cases h : ∃ t, FiniteRun f x t
  · obtain ⟨t, ht⟩ := h
    exact ⟨t, .inl ht⟩
  · let InfiniteState := {z : X // ¬∃ t, FiniteRun f z t}
    have next (z : InfiniteState) :
        ∃ z' : InfiniteState, ∃ w, Sum.inl (w, Sum.inr z'.1) ∈ (f z.1).1 := by
      obtain ⟨t, ht⟩ := (f z.1).2
      rcases t with ⟨w, y | y⟩ | seq
      · exact (z.2 ⟨_, FiniteRun.ret ht⟩).elim
      · have hn : ¬ ∃ t, FiniteRun f y t := by
          rintro ⟨t, hr⟩
          exact z.2 ⟨_, FiniteRun.step ht hr⟩
        exact ⟨⟨y, hn⟩, w, ht⟩
      · exact (z.2 ⟨_, FiniteRun.stop ht⟩).elim
    let states : ℕ → InfiniteState := Nat.rec ⟨x, h⟩ (fun _ z => (next z).choose)
    let p : InfiniteRun f x :=
      ⟨fun i => (states i).1, fun i => (next (states i)).choose_spec.choose, rfl,
        fun i => (next (states i)).choose_spec.choose_spec⟩
    exact ⟨_, .inr ⟨p, (realizes_eq p _).2 rfl⟩⟩

theorem runs_fixpoint (f : X → Traces A (Y ⊕ X)) (x : X) (t : Model A Y) :
    Runs f x t ↔ t ∈ bindSet (f x).1 (Sum.elim (fun y => {Sum.inl ([], y)})
      (fun z => {s | Runs f z s})) := by
  constructor
  · rintro (hr | ⟨p, hp⟩)
    · cases hr with
      | ret h =>
        exact ⟨_, h, .inl ([], _), rfl, congrArg (fun w => Sum.inl (w, _)) (List.append_nil _)⟩
      | stop h => exact ⟨_, h, rfl⟩
      | step h hr => exact ⟨_, h, _, Or.inl hr, rfl⟩
    · have edge := p.edge 0
      rw [p.start] at edge
      rw [realizes_eq] at hp
      subst t
      refine ⟨_, edge, .inr (chunks (tailRun p).word), Or.inr ⟨tailRun p, (realizes_eq _ _).2 rfl⟩, ?_⟩
      exact congrArg Sum.inr (chunk_head p.word).symm
  · rintro ⟨s, hs, ht⟩
    rcases s with ⟨w, y | z⟩ | seq
    · obtain ⟨u, hu, rfl⟩ := ht
      change u = Sum.inl ([], y) at hu
      subst u
      change Runs f x (.inl (w ++ [], y))
      rw [List.append_nil]
      exact .inl (.ret hs)
    · obtain ⟨u, hu, rfl⟩ := ht
      rcases hu with hr | ⟨p, hp⟩
      · exact .inl (.step hs hr)
      · rw [realizes_eq] at hp
        subst u
        refine .inr ⟨consRun hs p, (realizes_eq _ _).2 ?_⟩
        exact congrArg Sum.inr (chunk_head (consRun hs p).word).symm
    · change t = .inr seq at ht
      subst t
      exact .inl (.stop hs)

theorem silent_loop_hangs (A Y : Type u) :
    Runs (fun x : PUnit.{u + 1} => (pure (Sum.inr x) : Traces A (Y ⊕ PUnit.{u + 1})))
      PUnit.unit (.inr Stream'.Seq.nil) := by
  refine .inr ⟨⟨fun _ => PUnit.unit, fun _ => [], rfl, fun _ => rfl⟩, ?_⟩
  refine ⟨Stream'.Seq.nil, rfl, fun n => ?_⟩
  change none = chunkAt (fun _ => []) n
  have emptyPrefix (k : ℕ) : wordsPrefix (fun _ => ([] : List A)) k = [] := by
    induction k with
    | zero => rfl
    | succ k ih => exact ih
  apply Eq.symm
  apply Option.eq_none_iff_forall_not_mem.2
  intro a ha
  obtain ⟨k, hk⟩ := (chunkAt_some _ n a).mp ha
  rw [emptyPrefix] at hk
  contradiction

end Silmaril.Calco2019.Examples.Printing.HangTraces.Proofs
