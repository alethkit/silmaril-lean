module

public import Silmaril.Logic.Operational.SOS.Marked.Thms

@[expose] public section

namespace Silmaril.Logic.Operational.SOS.Marked

open CategoryTheory
open Silmaril.Semantics.Operational (HasOpSem OpSem)

universe u

/-- The distinguished UB predicate of an interpreted marked system. -/
def WithMarker.ub (M : WithMarker.{u}) : M.carriers.State → Prop :=
  M.model ∘ ubJudgment

/-- Existentially hide raw labels for the existing finite policy interface.
The endpoint predicate is supplied directly by the interpreted tags. -/
def Ordinary.toOpSem (M : Ordinary.{u}) : OpSem M.carriers.State M.carriers.Observation where
  step s t := ∃ l, M.model (.step (s, l, t))
  observe s o := M.model (.endpoint s o)

/-- The raw operational policy supplied by the marked tags. -/
def WithMarker.toHasOpSem (M : WithMarker.{u}) :
    HasOpSem M.carriers.Program M.carriers.State M.carriers.Observation where
  initial p s := (forget.obj M).model (.entry p s)
  semantics := ⟨(forget.obj M).toOpSem, M.ub⟩

namespace Interpretation.Hom

/-- Every target edge out of a mapped state lifts, including its label and
endpoint. This is an additional condition on a forward map. -/
def LiftsSteps {M N : WithMarker.{u}} (f : M ⟶ N) : Prop :=
  ∀ s l t, N.system.model (f.carriers.signature.state s, l, t) →
    ∃ k v, M.system.model (s, k, v) ∧
      f.carriers.signature.label k = l ∧ f.carriers.signature.state v = t

/-- The marker predicate is reflected at every mapped state. -/
def ReflectsUB {M N : WithMarker.{u}} (f : M ⟶ N) : Prop :=
  ∀ s, N.ub (f.carriers.signature.state s) → M.ub s

end Interpretation.Hom

end Silmaril.Logic.Operational.SOS.Marked
