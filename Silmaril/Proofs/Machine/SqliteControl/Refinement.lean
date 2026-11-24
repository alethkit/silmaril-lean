module

public import Silmaril.Machine.SqliteControl.Defs

public section

namespace Silmaril.Proofs.Machine.SqliteControl

open Silmaril.Machine.SqliteControl

private theorem eraseAdvance (cfg : Config Call) (tid : Thread) (pc : Call) (shared : Shared) :
    erase (cfg.advance tid pc shared) = (erase cfg).advance tid pc.erase shared := by
  simp only [erase, Config.advance]
  congr
  funext other
  split <;> rfl

private theorem advanceSilent (cfg : Config Call) (tid : Thread) (pc : Call)
    (h : pc.erase = (cfg.threads tid).erase) :
    erase (cfg.advance tid pc) = erase cfg := by
  rw [eraseAdvance, h]
  simp only [Config.advance, erase]
  congr
  funext other
  split <;> simp_all

private theorem stepRefines {cfg after : Config Call} {event : Option Event}
    (h : CallStep cfg event after) :
    match event with
    | none => erase after = erase cfg
    | some label => Step (erase cfg) (some label) (erase after) := by
  obtain ⟨tid, input, h⟩ := h
  generalize hinput : input = selected at h
  cases hpc : cfg.threads tid <;> cases selected <;>
    simp only [callStep, hpc, Option.isNone_iff_eq_none, reduceCtorEq] at h
  all_goals
    (try split at h) <;> simp at h
    obtain ⟨rfl, rfl⟩ := h
    first
    | exact advanceSilent cfg tid _ (by rw [hpc]; rfl)
    | refine ⟨tid, input, _, rfl, ?_⟩
      have herase : (erase cfg).threads tid = (cfg.threads tid).erase := rfl
      unfold step
      rw [herase, hpc, hinput, eraseAdvance]
      simp_all [Call.erase, erase]

theorem runRefines {cfg after : Config Call} {events : List Event}
    (h : Run CallStep cfg events after) : Run Step (erase cfg) events (erase after) := by
  induction h with
  | done cfg => exact .done (erase cfg)
  | @more cfg middle after event rest first _ tail =>
    have hstep := stepRefines first
    cases event with
    | none => simpa [hstep] using tail
    | some label => exact .more hstep tail

end Silmaril.Proofs.Machine.SqliteControl
