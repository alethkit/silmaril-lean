module

public import Silmaril.Semantics.Page.Trace.Defs
import Silmaril.Semantics.Page.Thms

public section
namespace Silmaril.Proofs.Semantics.Page

open Silmaril.Semantics.Page

universe u v w x y
variable {Id : Type u} {Content : Type v} {Memory : Type w} {Other : Type x} {access : Access Id Content Memory}
variable {trace first last : Trace Id Content} {page : Id}
variable {initial middle final : Memory}

theorem reads_append :
    (first ++ last).reads = first.reads ++ last.reads := by
  simp [Trace.reads]

theorem writes_append :
    (first ++ last).writes = first.writes ++ last.writes := by
  simp [Trace.writes]

theorem reads_toTrace (reads : ReadTrace Id Content) :
    reads.toTrace.reads = reads := by
  induction reads with
  | nil => rfl
  | cons entry rest ih => simpa [ReadTrace.toTrace, Trace.reads] using ih

theorem writes_toTrace (writes : WriteTrace Id Content) :
    writes.toTrace.writes = writes := by
  induction writes with
  | nil => rfl
  | cons entry rest ih => simpa [WriteTrace.toTrace, Trace.writes] using ih

theorem readOnly_reads (trace : Trace Id Content) : trace.reads.toTrace.ReadOnly := by
  simp [Trace.ReadOnly, reads_toTrace]

theorem writeOnly_writes (trace : Trace Id Content) : trace.writes.toTrace.WriteOnly := by
  simp [Trace.WriteOnly, writes_toTrace]

theorem defs_append :
    (first ++ last).Defs page ↔ first.Defs page ∨ last.Defs page := by
  simp only [Trace.Defs, writes_append, List.mem_append, exists_or]

theorem footprint_append :
    (first ++ last).Footprint page ↔ first.Footprint page ∨ last.Footprint page := by
  simp only [Trace.Footprint, Trace.Reads, reads_append, List.mem_append, exists_or, defs_append]
  grind

theorem uses_append :
    (first ++ last).Uses page ↔ first.Uses page ∨ (¬ first.Defs page ∧ last.Uses page) := by
  induction first with
  | nil => simp [Trace.Uses, Trace.Defs, Trace.writes]
  | cons event rest ih =>
    cases event <;> simp only [List.cons_append, Trace.Uses, ih, Trace.Defs,
      Trace.writes, List.filterMap_cons, List.mem_cons, Prod.mk.injEq] <;> grind

theorem uses_or_defs : trace.Uses page ∨ trace.Defs page ↔ trace.Footprint page := by
  induction trace with
  | nil => simp [Trace.Uses, Trace.Footprint, Trace.Reads, Trace.Defs, Trace.reads, Trace.writes]
  | cons event rest ih =>
    cases event <;>
      simp only [Trace.Uses, Trace.Footprint, Trace.Reads, Trace.Defs, Trace.reads, Trace.writes,
        List.filterMap_cons, List.mem_cons,
        Prod.mk.injEq] at ih ⊢ <;> grind

theorem replays_append :
    (first ++ last).Replays access initial final ↔
      ∃ middle, first.Replays access initial middle ∧ last.Replays access middle final := by
  induction first generalizing initial with
  | nil => simp [Trace.Replays]
  | cons event rest ih =>
    cases event <;> simp only [List.cons_append, Trace.Replays, ih] <;> grind

theorem run_eq_some_iff [DecidableEq Content] :
    trace.run access initial = some final ↔ trace.Replays access initial final := by
  induction trace generalizing initial with
  | nil => simp [Trace.run, Trace.Replays]
  | cons event rest ih =>
    cases event with
    | read page value =>
      by_cases h : access.read initial page = some value <;> simp [Trace.run, Trace.Replays, h, ih]
    | write page value =>
      cases h : access.write initial page value <;> simp [Trace.run, Trace.Replays, h, ih]

theorem replays_unique (left : trace.Replays access initial middle)
    (right : trace.Replays access initial final) : middle = final := by
  induction trace generalizing initial with
  | nil => exact left.symm.trans right
  | cons event rest ih =>
    cases event with
    | read => exact ih left.2 right.2
    | write =>
      obtain ⟨next, step, tail⟩ := left
      obtain ⟨next', step', tail'⟩ := right
      rw [step] at step'
      cases Option.some.inj step'
      exact ih tail tail'

theorem replays_map {other : Access Id Content Other} (f : Memory → Other)
    (read : ∀ m p, other.read (f m) p = access.read m p)
    (write : ∀ m p v, other.write (f m) p v = (access.write m p v).map f)
    {target : Other} :
    trace.Replays other (f initial) target ↔
      ∃ final, trace.Replays access initial final ∧ f final = target := by
  induction trace generalizing initial with
  | nil => simp [Trace.Replays]
  | cons event rest ih =>
    cases event with
    | read p v => simp only [Trace.Replays, read, ih]; grind
    | write p v =>
      cases h : access.write initial p v <;>
        simp [Trace.Replays, write, h, ih]

theorem run_map [DecidableEq Content] {other : Access Id Content Other} (f : Memory → Other)
    (read : ∀ m p, other.read (f m) p = access.read m p)
    (write : ∀ m p v, other.write (f m) p v = (access.write m p v).map f) :
    trace.run other (f initial) = (trace.run access initial).map f := by
  induction trace generalizing initial with
  | nil => rfl
  | cons event rest ih =>
    cases event with
    | read p v =>
      by_cases h : access.read initial p = some v <;> simp [Trace.run, read, h, ih]
    | write p v =>
      cases h : access.write initial p v <;> simp [Trace.run, write, h, ih]

theorem replays_readTrace (reads : ReadTrace Id Content) :
    reads.toTrace.Replays access initial final ↔ initial = final ∧ reads.Agrees access initial := by
  induction reads with
  | nil => simp [ReadTrace.toTrace, Trace.Replays, ReadTrace.Agrees]
  | cons entry rest ih =>
    rcases entry with ⟨p, v⟩
    change (access.read initial p = some v ∧ Trace.Replays access (ReadTrace.toTrace rest) initial final) ↔ _
    rw [ih]
    simp [ReadTrace.Agrees, and_left_comm]

theorem replays_writes (run : trace.Replays access initial final) :
    trace.writes.toTrace.Replays access initial final := by
  induction trace generalizing initial with
  | nil => exact run
  | cons event rest ih =>
    cases event with
    | read => exact ih run.2
    | write =>
      obtain ⟨m, h, tail⟩ := run
      exact ⟨m, h, ih tail⟩

theorem store_write_iff {store : Store Id Content Memory} {value : Content} :
    store.access.write initial page value = some middle ↔
      store.domain initial page ∧ store.set initial page (.defined value) = middle := by
  cases h : store.lookup initial page <;> simp [Store.access, Store.domain, h]

theorem store_read_iff {store : Store Id Content Memory} {value : Content} :
    store.access.read initial page = some value ↔ store.lookup initial page = .defined value := by
  cases h : store.lookup initial page <;> simp [Store.access, Slot.value, h]

theorem replays_frame {store : Store Id Content Memory}
    (run : trace.Replays store.access initial final) (outside : ¬ trace.Defs page) :
    store.lookup final page = store.lookup initial page := by
  induction trace generalizing initial with
  | nil =>
    change initial = final at run
    rw [run]
  | cons event rest ih =>
    cases event with
    | read => exact ih run.2 outside
    | write p v =>
      obtain ⟨next, step, tail⟩ := run
      obtain ⟨_, rfl⟩ := store_write_iff.mp step
      have notDef : page ≠ p ∧ ¬Trace.Defs rest page := by
        simpa [Trace.Defs, Trace.writes, Prod.mk.injEq, exists_or] using outside
      exact (ih tail notDef.2).trans (store.lookup_set_other _ _ _ _ notDef.1)

theorem replays_use_defined {store : Store Id Content Memory}
    (run : trace.Replays store.access initial final) (used : trace.Uses page) :
    ∃ value, store.lookup initial page = .defined value := by
  induction trace generalizing initial with
  | nil => exact False.elim used
  | cons event rest ih =>
    cases event with
    | read p v =>
      rcases used with eq | tailUse
      · subst p
        exact ⟨v, store_read_iff.mp run.1⟩
      · exact ih run.2 tailUse
    | write p v =>
      obtain ⟨next, step, tail⟩ := run
      obtain ⟨_, rfl⟩ := store_write_iff.mp step
      obtain ⟨value, defined⟩ := ih tail used.2
      exact ⟨value, (store.lookup_set_other _ _ _ _ used.1).symm.trans defined⟩

theorem reads_agree_of_disjoint {store : Store Id Content Memory}
    (run : trace.Replays store.access initial final)
    (disjoint : ∀ p, trace.Reads p → ¬ trace.Defs p) :
    trace.reads.Agrees store.access initial := by
  intro entry present
  rcases entry with ⟨page, value⟩
  induction trace generalizing initial with
  | nil => cases present
  | cons event rest ih =>
    cases event with
    | read p v =>
      change (page, value) ∈ (p, v) :: Trace.reads rest at present
      rcases List.mem_cons.mp present with eq | member
      · cases eq
        exact run.1
      · have tailDisjoint : ∀ q, Trace.Reads rest q → ¬Trace.Defs rest q := by
          rintro q ⟨v', hv⟩
          exact disjoint q ⟨v', List.mem_cons_of_mem _ hv⟩
        exact ih run.2 tailDisjoint member
    | write p v =>
      obtain ⟨next, step, tail⟩ := run
      obtain ⟨_, rfl⟩ := store_write_iff.mp step
      have ne : page ≠ p := by
        intro eq
        subst p
        exact disjoint page ⟨value, present⟩ ⟨v, List.mem_cons_self⟩
      have tailDisjoint : ∀ q, Trace.Reads rest q → ¬Trace.Defs rest q := by
        rintro q h ⟨v', hv⟩
        exact disjoint q h ⟨v', List.mem_cons_of_mem _ hv⟩
      have agrees := ih tail tailDisjoint present
      simpa only [Store.access, store.lookup_set_other _ _ _ _ ne] using agrees

theorem records_run {Result : Type y} {M : Model Id Content Memory} {program : Program Id Content Result}
    {result : Result} (path : Program.Records program trace result)
    (run : trace.Replays M.store.access initial final) :
    Run M program initial trace.writes.edits (.returned result final) := by
  induction path generalizing initial with
  | pure =>
    change initial = final at run
    cases run
    exact .pure
  | left _ ih => exact .left (ih run)
  | right _ ih => exact .right (ih run)
  | read _ ih => exact .call (.readDefined (store_read_iff.mp run.1)) (ih run.2)
  | write _ ih =>
    obtain ⟨next, step, tail⟩ := run
    obtain ⟨allocated, rfl⟩ := store_write_iff.mp step
    exact .call (.write allocated) (ih tail)

theorem replay_completion [DecidableEq Id] {M : Model Id Content Memory}
    {image : Image Id Content} (run : trace.Replays M.store.access initial final)
    (complete : Completion M initial image) :
    ∃ target, Replay trace.writes.edits image target ∧ Completion M final target := by
  induction trace generalizing initial image with
  | nil =>
    change initial = final at run
    cases run
    exact ⟨image, .nil, complete⟩
  | cons event rest ih =>
    cases event with
    | read => exact ih run.2 complete
    | write p v =>
      obtain ⟨next, step, tail⟩ := run
      obtain ⟨allocated, rfl⟩ := store_write_iff.mp step
      have completion := step_completion (M := M)
        (Step.write (value := v) allocated) complete (.cons rfl .nil)
      obtain ⟨target, replay, completed⟩ := ih tail completion
      exact ⟨target, .cons rfl replay, completed⟩

end Silmaril.Proofs.Semantics.Page
