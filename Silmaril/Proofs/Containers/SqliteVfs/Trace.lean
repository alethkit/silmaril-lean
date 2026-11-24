module

public import Silmaril.Containers.SqliteVfs.Defs

public section

namespace Silmaril.Proofs.Containers.SqliteVfs

open Silmaril.Containers
open Silmaril.Containers.SqliteVfs
open Silmaril.Machine.SqliteVfs

variable {State : Type} {handler : Handler State}

private theorem exec_shape {start finish : (machine handler).State} {events : List Event}
    (run : (machine handler).Exec Mach.seqPolicy start events finish) :
    match events with
    | [] => start = finish
    | event :: rest =>
      ∃ middle, Step handler start (.ev event) middle ∧
        (machine handler).Exec Mach.seqPolicy middle rest finish := by
  cases run with
  | refl => rfl
  | internal hidden edge _ => cases edge <;> cases hidden
  | ev edge tail => exact ⟨_, edge, tail⟩

private theorem exec_encoded {start finish : State} {trace : Trace}
    (valid : Trace.Valid handler start trace finish) :
    (machine handler).Exec Mach.seqPolicy (.idle start) (encode trace) (.idle finish) := by
  induction valid with
  | nil => exact .refl _
  | cons next _ tail => exact .ev (.recv ..) (.ev (.send next) tail)

private theorem exec_explained (events : List Event) {start : State} {finish : Phase State}
    (run : (machine handler).Exec Mach.seqPolicy (.idle start) events finish) :
    ∃ trace current, Trace.Valid handler start trace current ∧
      ((events = encode trace ∧ finish = .idle current) ∨
        ∃ request, events = encode trace ++ [.recv request] ∧ finish = .pending current request) := by
  match events with
  | [] => exact ⟨[], start, .nil _, .inl ⟨rfl, (exec_shape run).symm⟩⟩
  | [event] =>
    obtain ⟨_, receive, tail⟩ := exec_shape run
    cases receive with
    | recv state request => exact ⟨[], start, .nil _, .inr ⟨request, rfl, (exec_shape tail).symm⟩⟩
  | first :: second :: rest =>
    obtain ⟨_, receive, tail⟩ := exec_shape run
    cases receive with
    | recv state request =>
      obtain ⟨_, send, tail⟩ := exec_shape tail
      cases send with
      | send next =>
        obtain ⟨trace, current, valid, complete | pending⟩ := exec_explained rest tail
        · exact ⟨_ :: trace, current, .cons next valid,
            .inl ⟨by simpa [encode] using complete.1, complete.2⟩⟩
        · obtain ⟨last, append, ends⟩ := pending
          exact ⟨_ :: trace, current, .cons next valid,
            .inr ⟨last, by simpa [encode] using append, ends⟩⟩

theorem exec_iff {start : State} {events : List Event} {finish : Phase State} :
    (machine handler).Exec Mach.seqPolicy (.idle start) events finish ↔
      ∃ trace current, Trace.Valid handler start trace current ∧
        ((events = encode trace ∧ finish = .idle current) ∨
          ∃ request, events = encode trace ++ [.recv request] ∧ finish = .pending current request) := by
  constructor
  · exact exec_explained events
  · rintro ⟨trace, current, valid, complete | pending⟩
    · obtain ⟨rfl, rfl⟩ := complete
      exact exec_encoded valid
    · obtain ⟨request, rfl, rfl⟩ := pending
      induction valid with
      | nil => exact .ev (.recv ..) (.refl _)
      | cons next _ tail => exact .ev (.recv ..) (.ev (.send next) tail)

private theorem idle_waiting (state : State) : (machine handler).Waiting (.idle state) := by
  refine ⟨fun _ impossible => impossible, ⟨.recv (.openFile .readOnly), _, rfl, .recv ..⟩, ?_⟩
  intro action next edge
  change Step handler (.idle state) action next at edge
  cases edge
  exact ⟨_, rfl, rfl⟩

private theorem pending_not_waiting (state : State) (request : Request) :
    ¬ (machine handler).Waiting (.pending state request) := by
  intro waiting
  have edge : Step handler (.pending state request)
      (.ev (.send ⟨request, (handler state request).1⟩)) (.idle (handler state request).2) :=
    .send (Prod.eta _).symm
  obtain ⟨event, label, input⟩ := waiting.2.2 _ _ edge
  cases label
  contradiction

theorem blocked_iff {start : State} {events : List Event} :
    (runtime handler).beh start (.blocked events) ↔
      ∃ trace finish, Trace.Valid handler start trace finish ∧ events = encode trace := by
  change (∃ b, (machine handler).Run Mach.seqPolicy start b ∧ b = .blocked events) ↔ _
  constructor
  · rintro ⟨_, run, rfl⟩
    cases run with
    | blocked loaded executed waiting =>
      change _ = Phase.idle start at loaded
      subst_vars
      obtain ⟨trace, current, valid, complete | pending⟩ := exec_iff.mp executed
      · exact ⟨trace, current, valid, complete.1⟩
      · obtain ⟨request, _, rfl⟩ := pending
        exact (pending_not_waiting current request waiting).elim
  · rintro ⟨trace, finish, valid, rfl⟩
    exact ⟨_, .blocked rfl (exec_encoded valid) (idle_waiting finish), rfl⟩

end Silmaril.Proofs.Containers.SqliteVfs
