module

public import Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Theta.Defs
public import Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Thms
public import Silmaril.SSA.RVSDG.Theta.Thms

public section

namespace Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Theta.Proofs

open CategoryTheory Silmaril.Elgot

universe u v w k
variable {V : Type u} {P E : Dialect.{u, v} V PUnit.{u + 1}}
variable {carried : Ports (Ty V)} {sigs : List (Ports (Ty V))}
variable {ρ : Type (max u w)}

set_option backward.isDefEq.respectTransparency false

theorem close_of {N : Type k → Type k} [_root_.Monad N] [LawfulMonad N] [Iterate N]
    {A : Type k} (f : A → N (A ⊕ A)) : ⇑(close f).of = iter f := by
  unfold close
  rw [Kleisli.Type.iterate_of]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

variable (m : Model P E (StateM ρ)) (g : Loop (P := P) (E := E) (carried := carried) (sigs := sigs))
variable {data : Data carried} (checked : BodyChecked data g)

private theorem decode_injective :
    Function.Injective (decode (value := m.value) (ts := carried) (ρ := ρ)) :=
  fun _ _ h => (encode_decode _).symm.trans ((congrArg encode h).trans (encode_decode _))

private theorem tagged_iff (input output : Tuple (Values m.value) carried × ρ)
    (requested actual : Bool) :
    (if requested then Sum.inr output else Sum.inl output : _ ⊕ _) =
      (if actual then Sum.inr input else Sum.inl input) ↔
      RVSDG.Theta.bodyResult m.toRVSDG actual (decode input) =
        RVSDG.Theta.bodyResult m.toRVSDG requested (decode output) := by
  cases requested <;> cases actual <;>
    simp [RVSDG.Theta.bodyResult, Tuple.cons.injEq, (decode_injective m).eq_iff, eq_comm]
  all_goals
    intro h
    exact (Nat.zero_ne_one (congrArg (fun tag : ULift (Fin 2) => tag.down.val) h)).elim

private theorem body_member (input output : Tuple (Values m.value) carried × ρ) (again : Bool) :
    (if again then Sum.inr output else Sum.inl output) ∈
        Silmaril.Elgot.StateT.body (totalStep m g checked) input ↔
      g.body.run m.toRVSDG (decode input) =
        RVSDG.Theta.bodyResult m.toRVSDG again (decode output) := by
  have sim := denoteGraph_run m (args := carried) (outs := .control 2 :: carried)
    (a := data) (b := Data.control (n := 2) data) g.body checked (decode input)
  rw [encode_decode] at sim
  rw [← sim]
  rcases evaluated : (bodyComputation m g checked input.1).run input.2 with ⟨result, nextState⟩
  cases result with
  | cons tag payload =>
    have one : Silmaril.Elgot.StateT.body (totalStep m g checked) input =
        _root_.Part.some (Silmaril.Elgot.StateT.distribute (route.{u, w} (.cons tag payload), nextState)) := by
      change (_root_.Part.some (route.{u, w} ((bodyComputation m g checked input.1).run input.2).1,
        ((bodyComputation m g checked input.1).run input.2).2) >>= fun x =>
          _root_.Part.some (Silmaril.Elgot.StateT.distribute x)) = _
      rw [evaluated]
      simp
    rw [one, _root_.Part.mem_some_iff]
    obtain ⟨tag⟩ := tag
    refine Fin.cases ?_ (fun j => ?_) tag
    · exact tagged_iff m (payload, nextState) output again false
    · have hj : j = 0 := Fin.eq_zero j
      subst j
      exact tagged_iff m (payload, nextState) output again true

private theorem runs_returns {input output : Tuple (Values m.value) carried × ρ}
    (h : Silmaril.Elgot.Part.Runs (Silmaril.Elgot.StateT.body (totalStep m g checked)) input output) :
    g.Returns m.toRVSDG (decode input) (decode output) := by
  induction h with
  | done step => exact .stop ((body_member m g checked _ _ false).mp step)
  | more step _ ih => exact .again ((body_member m g checked _ _ true).mp step) ih

private theorem returns_runs {input output : Tuple (RuntimeValues m.value ρ) (Threaded carried)}
    (h : g.Returns m.toRVSDG input output) :
    Silmaril.Elgot.Part.Runs (Silmaril.Elgot.StateT.body (totalStep m g checked))
      (encode input) (encode output) := by
  induction h with
  | stop step =>
    apply Silmaril.Elgot.Part.Runs.done
    apply (body_member m g checked _ _ false).mpr
    simpa only [decode_encode data] using step
  | again step _ ih =>
    apply Silmaril.Elgot.Part.Runs.more _ ih
    apply (body_member m g checked _ _ true).mpr
    simpa only [decode_encode data] using step

theorem mem_denote (input output : Tuple (RuntimeValues m.value ρ) (Threaded carried)) :
    output ∈ denoteTotal m g checked input ↔ g.Returns m.toRVSDG input output := by
  change output ∈ _root_.Part.map decode (((close (totalStep m g checked)).of
    (encode input).1).run (encode input).2) ↔ _
  rw [close_of, Silmaril.Elgot.StateT.run_iter, _root_.Part.mem_map_iff]
  constructor
  · rintro ⟨pair, h, rfl⟩
    have execution := (Silmaril.Elgot.Part.mem_iter_iff _ _ _).mp h
    change Silmaril.Elgot.Part.Runs _ (encode input) pair at execution
    simpa only [decode_encode data] using runs_returns m g checked execution
  · intro h
    exact ⟨encode output, (Silmaril.Elgot.Part.mem_iter_iff _ _ _).mpr
      (returns_runs m g checked h), decode_encode data output⟩

private def after (input : Tuple (RuntimeValues m.value ρ) (Threaded carried)) :
    Tuple (RuntimeValues m.value ρ) (Threaded carried) :=
  match g.body.run m.toRVSDG input with
  | .cons _ values => values

private theorem step_cases (input : Tuple (RuntimeValues m.value ρ) (Threaded carried)) :
    g.body.run m.toRVSDG input = RVSDG.Theta.bodyResult m.toRVSDG false (after m g input) ∨
    g.body.run m.toRVSDG input = RVSDG.Theta.bodyResult m.toRVSDG true (after m g input) := by
  unfold after
  generalize g.body.run m.toRVSDG input = result
  cases result with
  | cons tag values =>
    cases tag with
    | up key =>
      have keys : key = 0 ∨ key = 1 := by
        refine Fin.cases (Or.inl rfl) (fun i => ?_) key
        rw [Fin.eq_zero i]
        exact Or.inr rfl
      rcases keys with zero | one
      · exact Or.inl (by rw [zero]; rfl)
      · exact Or.inr (by rw [one]; rfl)

private theorem repeats_of_no_return (input : Tuple (RuntimeValues m.value ρ) (Threaded carried))
    (none : ∀ output, ¬g.Returns m.toRVSDG input output) : g.Diverges m.toRVSDG input := by
  have advance (state : Tuple (RuntimeValues m.value ρ) (Threaded carried))
      (noReturn : ∀ output, ¬g.Returns m.toRVSDG state output) :
      g.body.run m.toRVSDG state = RVSDG.Theta.bodyResult m.toRVSDG true (after m g state) ∧
        ∀ output, ¬g.Returns m.toRVSDG (after m g state) output := by
    rcases step_cases m g state with stop | again
    · exact (noReturn _ (.stop stop)).elim
    · exact ⟨again, fun output execution => noReturn output (.again again execution)⟩
  let stream : Nat → Tuple (RuntimeValues m.value ρ) (Threaded carried) :=
    Nat.rec input (fun _ state => after m g state)
  have invariant (n : Nat) : ∀ output, ¬g.Returns m.toRVSDG (stream n) output := by
    induction n with
    | zero => exact none
    | succ n ih => exact (advance (stream n) ih).2
  exact ⟨stream, rfl, fun n => (advance (stream n) (invariant n)).1⟩

theorem none_iff (input : Tuple (RuntimeValues m.value ρ) (Threaded carried)) :
    denoteTotal m g checked input = _root_.Part.none ↔ g.Diverges m.toRVSDG input := by
  rw [_root_.Part.eq_none_iff]
  constructor
  · intro missing
    exact repeats_of_no_return m g input
      (fun output returns => missing output ((mem_denote m g checked input output).mpr returns))
  · intro diverges output returns
    exact g.not_diverges_of_returns m.toRVSDG
      ((mem_denote m g checked input output).mp returns) diverges

end Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Theta.Proofs
