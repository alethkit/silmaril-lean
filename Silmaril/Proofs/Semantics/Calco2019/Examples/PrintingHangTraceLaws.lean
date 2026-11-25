module

public import Silmaril.Semantics.Calco2019.Examples.Printing.HangTraces.Thms

public section

universe u

namespace Silmaril.Calco2019.Examples.Printing.HangTraces.LawProofs

open Hangs

variable {A X Y Z S : Type u}

private def mapResult (h : X → Y) : Model A X → Model A Y
  | .inl (w, x) => .inl (w, h x)
  | .inr seq => .inr seq

private theorem map_prepend (h : X → Y) (w : List A) (t : Model A X) :
    mapResult h (prependWord w t) = prependWord w (mapResult h t) := by
  rcases t with ⟨_, _⟩ | _ <;> rfl

private theorem extend_pure (h : X → Y) (t : Model A X) :
    extendSet (fun x => {Sum.inl ([], h x)}) t = {mapResult h t} := by
  rcases t with ⟨w, x⟩ | seq
  · ext s
    simp only [extendSet, Set.mem_image, Set.mem_singleton_iff, exists_eq_left, mapResult]
    change Sum.inl (w ++ [], h x) = s ↔ s = Sum.inl (w, h x)
    rw [List.append_nil, eq_comm]
  · rfl

private theorem extend_prepend (f : X → Set (Model A Y)) (w : List A) (t : Model A X) :
    extendSet f (prependWord w t) = prependWord w '' extendSet f t := by
  rcases t with ⟨v, x⟩ | seq
  · change prependWord (w ++ v) '' f x = prependWord w '' (prependWord v '' f x)
    rw [Set.image_image]
    exact congrArg (fun h => h '' f x) (funext (fun u => (prependWord_append w v u).symm))
  · change {prependWord w (.inr seq : Model A Y)} = prependWord w '' {.inr seq}
    exact Set.image_singleton.symm

private theorem bind_pure_image (p : Traces A X) (h : X → Y) :
    (p >>= (pure ∘ h)).1 = mapResult h '' p.1 := by
  ext t
  change (∃ s ∈ p.1, t ∈ extendSet (fun x => {Sum.inl ([], h x)}) s) ↔ _
  simp only [extend_pure, Set.mem_singleton_iff, Set.mem_image]
  exact exists_congr fun _ => and_congr_right' eq_comm

private theorem mapReturn_cases (f : X → Traces A (Y ⊕ X)) (g : Y → Traces A Z)
    (x : X) (t : Model A (Z ⊕ X)) :
    t ∈ (Elgot.mapReturn f g x).1 ↔
      (∃ w y u, Sum.inl (w, Sum.inl y) ∈ (f x).1 ∧ u ∈ (g y).1 ∧
        t = mapResult Sum.inl (prependWord w u)) ∨
      (∃ w z, Sum.inl (w, Sum.inr z) ∈ (f x).1 ∧ t = Sum.inl (w, Sum.inr z)) ∨
      ∃ seq, Sum.inr seq ∈ (f x).1 ∧ t = Sum.inr seq := by
  change (∃ r ∈ (f x).1, t ∈ extendSet
    (fun s => (Sum.elim (fun y => g y >>= pure ∘ Sum.inl) (pure ∘ Sum.inr) s).1) r) ↔ _
  constructor
  · rintro ⟨q, hq, ht⟩
    rcases q with ⟨w, y | z⟩ | seq
    · change t ∈ prependWord w '' ((g y >>= (pure ∘ Sum.inl)).1 : Set (Model A (Z ⊕ X))) at ht
      rw [bind_pure_image, Set.image_image] at ht
      obtain ⟨u, hu, rfl⟩ := ht
      exact .inl ⟨w, y, u, hq, hu, (map_prepend Sum.inl w u).symm⟩
    · obtain ⟨v, hv, rfl⟩ := ht
      change v = Sum.inl ([], .inr z) at hv
      subst v
      exact .inr (.inl ⟨w, z, hq, congrArg (fun w => (Sum.inl (w, Sum.inr z) : Model A (Z ⊕ X))) (List.append_nil w)⟩)
    · exact .inr (.inr ⟨seq, hq, ht⟩)
  · rintro (⟨w, y, u, hy, hu, rfl⟩ | ⟨w, z, hz, rfl⟩ | ⟨seq, hs, rfl⟩)
    · refine ⟨.inl (w, .inl y), hy, ?_⟩
      change mapResult Sum.inl (prependWord w u) ∈
        prependWord w '' ((g y >>= (pure ∘ Sum.inl)).1 : Set (Model A (Z ⊕ X)))
      rw [bind_pure_image, map_prepend]
      exact ⟨mapResult Sum.inl u, ⟨u, hu, rfl⟩, rfl⟩
    · exact ⟨.inl (w, .inr z), hz, .inl ([], .inr z), rfl,
        congrArg (fun w => (Sum.inl (w, Sum.inr z) : Model A (Z ⊕ X))) (List.append_nil w)⟩
    · exact ⟨.inr seq, hs, rfl⟩

private theorem mapReturn_recursive (f : X → Traces A (Y ⊕ X)) (g : Y → Traces A Z)
    (x z : X) (w : List A) :
    Sum.inl (w, Sum.inr z) ∈ (Elgot.mapReturn f g x).1 ↔
      Sum.inl (w, Sum.inr z) ∈ (f x).1 := by
  constructor
  · intro h
    rcases (mapReturn_cases f g _ _).1 h with
      ⟨v, y, u, _, _, eq⟩ | ⟨v, z', h, eq⟩ | ⟨seq, _, eq⟩
    · rcases u with ⟨suffix, result⟩ | _
      · change Sum.inl (w, Sum.inr z) =
          (Sum.inl (v ++ suffix, Sum.inl result) : Model A (Z ⊕ X)) at eq
        cases eq
      · contradiction
    · cases eq; exact h
    · contradiction
  · intro h
    exact (mapReturn_cases f g _ _).2 (.inr (.inl ⟨w, z, h, rfl⟩))

private theorem runs_step (f : X → Traces A (Y ⊕ X)) {x z : X} {w : List A} {t : Model A Y}
    (h : Sum.inl (w, Sum.inr z) ∈ (f x).1) (ht : Runs f z t) :
    Runs f x (prependWord w t) := by
  have eq := congrFun (iterate_fixpoint f) x
  change prependWord w t ∈ (iterate f x).1
  rw [eq]
  exact ⟨.inl (w, .inr z), h, t, ht, rfl⟩

private theorem mapReturn_runs_forward (f : X → Traces A (Y ⊕ X)) (g : Y → Traces A Z)
    {x : X} {t : Model A Z} (h : Runs (Elgot.mapReturn f g) x t) :
    ∃ u, Runs f x u ∧ t ∈ extendSet (fun y => (g y).1) u := by
  rcases h with h | ⟨p, hp⟩
  · induction h with
    | ret h =>
      rcases (mapReturn_cases f g _ _).1 h with
        ⟨v, y, u, hf, hg, eq⟩ | ⟨_, _, _, eq⟩ | ⟨_, _, eq⟩
      · rcases u with ⟨_, _⟩ | _
        · cases eq
          exact ⟨.inl (v, y), .inl (.ret hf), _, hg, rfl⟩
        · contradiction
      · cases eq
      · contradiction
    | stop h =>
      rcases (mapReturn_cases f g _ _).1 h with
        ⟨v, y, u, hf, hg, eq⟩ | ⟨_, _, _, eq⟩ | ⟨seq, hf, eq⟩
      · rcases u with ⟨_, _⟩ | _
        · contradiction
        · cases eq
          exact ⟨.inl (v, y), .inl (.ret hf), _, hg, rfl⟩
      · contradiction
      · cases eq
        exact ⟨_, .inl (.stop hf), rfl⟩
    | step h _ ih =>
      obtain ⟨u, hu, ht⟩ := ih
      exact ⟨prependWord _ u, runs_step f ((mapReturn_recursive f g _ _ _).1 h) hu,
        (extend_prepend _ _ u).symm ▸ ⟨_, ht, rfl⟩⟩
  · let q : InfiniteRun f x := ⟨p.state, p.word, p.start,
      fun i => (mapReturn_recursive f g _ _ _).1 (p.edge i)⟩
    obtain ⟨seq, rfl, obs⟩ := hp
    exact ⟨.inr seq, .inr ⟨q, seq, rfl, obs⟩, rfl⟩

private theorem mapReturn_runs_backward (f : X → Traces A (Y ⊕ X)) (g : Y → Traces A Z)
    {x : X} {u : Model A Y} (h : Runs f x u) {t : Model A Z}
    (ht : t ∈ extendSet (fun y => (g y).1) u) :
    Runs (Elgot.mapReturn f g) x t := by
  rcases h with h | ⟨p, hp⟩
  · induction h generalizing t with
    | ret h =>
      obtain ⟨v, hv, rfl⟩ := ht
      rcases v with ⟨w, z⟩ | seq
      · exact .inl (.ret ((mapReturn_cases f g _ _).2 (.inl ⟨_, _, _, h, hv, rfl⟩)))
      · exact .inl (.stop ((mapReturn_cases f g _ _).2 (.inl ⟨_, _, _, h, hv, rfl⟩)))
    | stop h =>
      have eq : t = Sum.inr _ := ht
      subst t
      exact .inl (.stop ((mapReturn_cases f g _ _).2 (.inr (.inr ⟨_, h, rfl⟩))))
    | step h _ ih =>
      rw [extend_prepend] at ht
      obtain ⟨v, hv, rfl⟩ := ht
      exact runs_step _ ((mapReturn_recursive f g _ _ _).2 h) (ih hv)
  · let q : InfiniteRun (Elgot.mapReturn f g) x := ⟨p.state, p.word, p.start,
      fun i => (mapReturn_recursive f g _ _ _).2 (p.edge i)⟩
    obtain ⟨seq, rfl, obs⟩ := hp
    have eq : t = Sum.inr seq := ht
    subst t
    exact .inr ⟨q, seq, rfl, obs⟩

theorem naturality (f : X → Traces A (Y ⊕ X)) (g : Y → Traces A Z) :
    (iterate f >=> g) = iterate (Elgot.mapReturn f g) := by
  funext x
  apply Subtype.ext
  ext t
  change (∃ u, Runs f x u ∧ t ∈ extendSet (fun y => (g y).1) u) ↔ Runs (Elgot.mapReturn f g) x t
  exact ⟨fun ⟨u, hu, ht⟩ => mapReturn_runs_backward f g hu ht, mapReturn_runs_forward f g⟩

private theorem uniform_rows (f : X → Traces A (Y ⊕ X)) (g : Z → Traces A (Y ⊕ Z))
    (h : X → Z) (comm : (f >=> Elgot.liftPure (Sum.map id h)) = (Elgot.liftPure h >=> g))
    (x : X) :
    (g (h x)).1 = mapResult (Sum.map id h) '' (f x).1 := by
  have eq := congrFun comm x
  change f x >>= (pure ∘ Sum.map id h) = pure (h x) >>= g at eq
  rw [pure_bind] at eq
  exact (congrArg Subtype.val eq).symm.trans (bind_pure_image (f x) (Sum.map id h))

private theorem uniform_result {p : Set (Model A (Y ⊕ X))} (h : X → Z)
    (w : List A) (y : Y) :
    Sum.inl (w, Sum.inl y) ∈ mapResult (Sum.map id h) '' p ↔ Sum.inl (w, Sum.inl y) ∈ p := by
  constructor
  · rintro ⟨t, ht, eq⟩
    rcases t with ⟨v, y' | x⟩ | seq
    · change Sum.inl (v, Sum.inl y') = (Sum.inl (w, Sum.inl y) : Model A (Y ⊕ Z)) at eq
      cases eq; exact ht
    · change Sum.inl (v, Sum.inr (h x)) = (Sum.inl (w, Sum.inl y) : Model A (Y ⊕ Z)) at eq
      cases eq
    · contradiction
  · exact fun ht => ⟨_, ht, rfl⟩

private theorem uniform_hang {p : Set (Model A (Y ⊕ X))} (h : X → Z) (s : Stream'.Seq A) :
    Sum.inr s ∈ mapResult (Sum.map id h) '' p ↔ Sum.inr s ∈ p := by
  constructor
  · rintro ⟨t, ht, eq⟩
    rcases t with ⟨_, _⟩ | s'
    · contradiction
    · change Sum.inr s' = (Sum.inr s : Model A (Y ⊕ Z)) at eq
      cases eq; exact ht
  · exact fun ht => ⟨_, ht, rfl⟩

private theorem uniform_recursive {p : Set (Model A (Y ⊕ X))} (h : X → Z)
    (w : List A) (z : Z) :
    Sum.inl (w, Sum.inr z) ∈ mapResult (Sum.map id h) '' p ↔
      ∃ x, h x = z ∧ Sum.inl (w, Sum.inr x) ∈ p := by
  constructor
  · rintro ⟨t, ht, eq⟩
    rcases t with ⟨v, y | x⟩ | seq
    · change Sum.inl (v, Sum.inl y) = (Sum.inl (w, Sum.inr z) : Model A (Y ⊕ Z)) at eq
      cases eq
    · change Sum.inl (v, Sum.inr (h x)) = (Sum.inl (w, Sum.inr z) : Model A (Y ⊕ Z)) at eq
      have d := Prod.mk.inj (Sum.inl.inj eq)
      have hw := d.1
      subst w
      exact ⟨x, Sum.inr.inj d.2, ht⟩
    · contradiction
  · rintro ⟨x, rfl, ht⟩
    exact ⟨_, ht, rfl⟩

private theorem uniform_finite_forward (f : X → Traces A (Y ⊕ X)) (g : Z → Traces A (Y ⊕ Z))
    (h : X → Z) (row : ∀ x, (g (h x)).1 = mapResult (Sum.map id h) '' (f x).1)
    {x : X} {t : Model A Y} (run : FiniteRun f x t) : FiniteRun g (h x) t := by
  induction run with
  | ret hr => exact .ret ((row _).symm ▸ (uniform_result h _ _).2 hr)
  | stop hr => exact .stop ((row _).symm ▸ (uniform_hang h _).2 hr)
  | step hr _ ih =>
    exact .step ((row _).symm ▸ (uniform_recursive h _ _).2 ⟨_, rfl, hr⟩) ih

private theorem uniform_finite_backward (f : X → Traces A (Y ⊕ X)) (g : Z → Traces A (Y ⊕ Z))
    (h : X → Z) (row : ∀ x, (g (h x)).1 = mapResult (Sum.map id h) '' (f x).1)
    {z : Z} {t : Model A Y} (run : FiniteRun g z t) :
    ∀ x, h x = z → FiniteRun f x t := by
  induction run with
  | ret hr =>
    intro x hx
    rw [← hx, row] at hr
    exact .ret ((uniform_result h _ _).1 hr)
  | stop hr =>
    intro x hx
    rw [← hx, row] at hr
    exact .stop ((uniform_hang h _).1 hr)
  | step hr _ ih =>
    intro x hx
    rw [← hx, row] at hr
    obtain ⟨next, hnext, edge⟩ := (uniform_recursive h _ _).1 hr
    exact .step edge (ih next hnext)

private theorem uniform_runs (f : X → Traces A (Y ⊕ X)) (g : Z → Traces A (Y ⊕ Z))
    (h : X → Z) (row : ∀ x, (g (h x)).1 = mapResult (Sum.map id h) '' (f x).1)
    (x : X) (t : Model A Y) : Runs f x t ↔ Runs g (h x) t := by
  constructor
  · rintro (run | ⟨p, hp⟩)
    · exact .inl (uniform_finite_forward f g h row run)
    · let q : InfiniteRun g (h x) :=
        ⟨h ∘ p.state, p.word, congrArg h p.start,
          fun i => (row _).symm ▸ (uniform_recursive h _ _).2 ⟨_, rfl, p.edge i⟩⟩
      exact .inr ⟨q, hp⟩
  · rintro (run | ⟨p, hp⟩)
    · exact .inl (uniform_finite_backward f g h row run x rfl)
    · classical
      let Fibre (i : ℕ) := {s : X // h s = p.state i}
      have liftEdge (i : ℕ) (s : Fibre i) :
          ∃ next : Fibre (i + 1), Sum.inl (p.word i, Sum.inr next.1) ∈ (f s.1).1 := by
        have edge := p.edge i
        rw [← s.2, row] at edge
        obtain ⟨next, hn, edge⟩ := (uniform_recursive h _ _).1 edge
        exact ⟨⟨next, hn⟩, edge⟩
      let lifted : ∀ i, Fibre i := Nat.rec ⟨x, p.start.symm⟩ (fun i s => (liftEdge i s).choose)
      let q : InfiniteRun f x :=
        ⟨fun i => (lifted i).1, p.word, rfl, fun i => (liftEdge i (lifted i)).choose_spec⟩
      exact .inr ⟨q, hp⟩

theorem uniformity (f : X → Traces A (Y ⊕ X)) (g : Z → Traces A (Y ⊕ Z))
    (h : X → Z) (comm : (f >=> Elgot.liftPure (Sum.map id h)) = (Elgot.liftPure h >=> g)) :
    iterate f = (Elgot.liftPure h >=> iterate g) := by
  funext x
  change iterate f x = pure (h x) >>= iterate g
  rw [pure_bind]
  apply Subtype.ext
  exact Set.ext (uniform_runs f g h (uniform_rows f g h comm) x)

end Silmaril.Calco2019.Examples.Printing.HangTraces.LawProofs
