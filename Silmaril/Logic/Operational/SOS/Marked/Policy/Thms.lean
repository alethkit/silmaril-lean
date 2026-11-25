module

public import Silmaril.Logic.Operational.SOS.Marked.Policy.Defs
public import Silmaril.Semantics.Operational.Policy.Thms
import Silmaril.Proofs.Logic.Operational.SOS.Marked.Policy

@[expose] public section

namespace Silmaril.Logic.Operational.SOS.Marked

open CategoryTheory
open Silmaril.Semantics.Operational (WithUB)

universe u

/-- Empty-marker extension makes the raw policy safe from every start. -/
theorem emptyMarker_safe (M : Ordinary.{u}) (s : M.carriers.State) :
    (emptyMarker.obj M).toHasOpSem.semantics.SafeAt s :=
  WithUB.ofOpSem_safe M.toOpSem s

namespace Interpretation.Hom

variable {M N : WithMarker.{u}} (f : M ⟶ N)

theorem mapReach {s t : M.carriers.State}
    (path : M.toHasOpSem.semantics.toOpSem.Reach s t) :
    N.toHasOpSem.semantics.toOpSem.Reach (f.carriers.signature.state s)
      (f.carriers.signature.state t) :=
  Proofs.mapReach f path

theorem liftReach (lifts : LiftsSteps f) {s : M.carriers.State} {t : N.carriers.State}
    (path : N.toHasOpSem.semantics.toOpSem.Reach (f.carriers.signature.state s) t) :
    ∃ v, M.toHasOpSem.semantics.toOpSem.Reach s v ∧ f.carriers.signature.state v = t :=
  Proofs.liftReach f lifts path

/-- Every raw marked map reflects safety, by preserving paths and UB. -/
theorem safe_of_safe {s : M.carriers.State}
    (safe : N.toHasOpSem.semantics.SafeAt (f.carriers.signature.state s)) :
    M.toHasOpSem.semantics.SafeAt s :=
  fun ⟨t, path, ub⟩ => safe ⟨_, mapReach f path, f.preserves (ubJudgment t) ub⟩

/-- Safety transfers forwards as well when each outgoing edge lifts and UB is
reflected at mapped states. -/
theorem safe_iff (lifts : LiftsSteps f) (reflects : ReflectsUB f) (s : M.carriers.State) :
    N.toHasOpSem.semantics.SafeAt (f.carriers.signature.state s) ↔
      M.toHasOpSem.semantics.SafeAt s :=
  ⟨safe_of_safe f, fun safe ⟨_, path, ub⟩ =>
    let ⟨_, lifted, eq⟩ := liftReach f lifts path
    safe ⟨_, lifted, reflects _ (eq.symm ▸ ub)⟩⟩

end Interpretation.Hom

end Silmaril.Logic.Operational.SOS.Marked
