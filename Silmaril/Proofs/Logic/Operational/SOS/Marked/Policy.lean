module

public import Silmaril.Logic.Operational.SOS.Marked.Policy.Defs

@[expose] public section

namespace Silmaril.Logic.Operational.SOS.Marked.Proofs

open CategoryTheory

universe u

variable {M N : WithMarker.{u}}

theorem mapReach (f : M ⟶ N) {s t : M.carriers.State}
    (path : M.toHasOpSem.semantics.toOpSem.Reach s t) :
    N.toHasOpSem.semantics.toOpSem.Reach (f.carriers.signature.state s)
      (f.carriers.signature.state t) := by
  induction path with
  | refl => exact .refl
  | @tail v w _ step ih =>
    obtain ⟨l, hl⟩ := step
    exact ih.tail ⟨f.carriers.signature.label l, f.preserves (.inl (.step (v, l, w))) hl⟩

theorem liftReach (f : M ⟶ N) (lifts : Interpretation.Hom.LiftsSteps f)
    {s : M.carriers.State} {t : N.carriers.State}
    (path : N.toHasOpSem.semantics.toOpSem.Reach (f.carriers.signature.state s) t) :
    ∃ v, M.toHasOpSem.semantics.toOpSem.Reach s v ∧ f.carriers.signature.state v = t := by
  induction path with
  | refl => exact ⟨s, .refl, rfl⟩
  | tail _ step ih =>
    obtain ⟨v, reach, rfl⟩ := ih
    obtain ⟨l, hl⟩ := step
    obtain ⟨k, w, edge, _, hmap⟩ := lifts v l _ hl
    exact ⟨w, reach.tail ⟨k, edge⟩, hmap⟩

end Silmaril.Logic.Operational.SOS.Marked.Proofs
