module

public import Silmaril.Languages.Python.Core.Defs
public import Silmaril.Semantics.Operational.Determinism.Fuel.Thms
public import Silmaril.Semantics.Operational.Program.Thms
import Silmaril.Proofs.Languages.Python.Core.Properties

public section

namespace Silmaril.Languages.Python.Core

open Semantics.Operational

variable {profile : Profile} {body : Body} {source target : State} {label : Option Completion}
  {outcome : Outcome Completion} {fuel : Nat}

theorem BinOp.eval_iff {op : BinOp} {left right : Int} {result : Completion} :
    op.eval left right = result ↔ op.Eval left right result :=
  Proofs.Languages.Python.Core.bin_eval_iff

theorem Expr.reduce_iff {expr : Expr} {next : Except Exception Expr} :
    expr.reduce = some next ↔ expr.Step next :=
  Proofs.Languages.Python.Core.reduce_iff

theorem State.advance_iff : source.advance = some (label, target) ↔ Step source label target :=
  Proofs.Languages.Python.Core.advance_iff

/-- Both the action and the successor of a primitive step are determined. -/
theorem Step.deterministic {other : State} {otherLabel : Option Completion}
    (left : Step source label target) (right : Step source otherLabel other) :
    label = otherLabel ∧ target = other :=
  Proofs.Languages.Python.Core.step_deterministic left right

theorem detFrom (profile : Profile) (start : State) : (semantics profile).toOpSem.DetFrom start :=
  Proofs.Languages.Python.Core.detFrom profile start

theorem terminal (profile : Profile) : (semantics profile).toOpSem.TerminalDiscipline :=
  Proofs.Languages.Python.Core.terminal profile

theorem Step.preserves (step : Step source label target) (supported : source.supported profile) :
    target.supported profile :=
  Proofs.Languages.Python.Core.step_preserves step supported

theorem Step.decreases (step : Step source label target) : target.budget < source.budget :=
  Proofs.Languages.Python.Core.step_decreases step

theorem Step.result_eq (step : Step source label target) : source.result = target.result :=
  Proofs.Languages.Python.Core.step_result step

theorem progress (supported : source.supported profile) :
    (∃ label target, (labelled profile).step source label target) ∨
      (semantics profile).observe source (.returned source.result) :=
  Proofs.Languages.Python.Core.progress supported

theorem noDiverges (profile : Profile) (source : State) :
    ¬ (semantics profile).toOpSem.Diverges source :=
  Proofs.Languages.Python.Core.noDiverges profile source

theorem finishes_in_budget (supported : source.supported profile) :
    ∃ length, length ≤ source.budget ∧
      StepsN (semantics profile).step length source (.finished source.result) :=
  Proofs.Languages.Python.Core.finishes_in_budget supported

theorem safe (supported : source.supported profile) : (semantics profile).SafeAt source :=
  Proofs.Languages.Python.Core.safe supported

theorem Body.start_iff : body.start? profile = some source ↔ (model profile).initial body source :=
  Proofs.Languages.Python.Core.start_iff

theorem noEntry_iff : (model profile).NoEntry body ↔ ¬ profile.supports body.value :=
  Proofs.Languages.Python.Core.noEntry_iff

theorem model_safe : ¬ (model profile).UBReachable body :=
  Proofs.Languages.Python.Core.model_safe

theorem model_may_iff :
    (model profile).May body outcome ↔ profile.supports body.value ∧ outcome = .returned body.value.eval :=
  Proofs.Languages.Python.Core.model_may_iff

theorem labelled_finishes_iff {log : List Completion} (supported : profile.supports body.value) :
    (labelled profile).Finishes body.start log outcome ↔
      log = [body.value.eval] ∧ outcome = .returned body.value.eval :=
  Proofs.Languages.Python.Core.labelled_finishes_iff supported

theorem State.pick_valid (state : State) :
    state.pick.Valid (WithUB.ofOpSem ordinary) state :=
  Proofs.Languages.Python.Core.pick_valid state

/-- The executable selector certified against the profile's relational semantics. -/
@[expose] def oracle (profile : Profile) : Oracle (semantics profile) :=
  let raw : Oracle (WithUB.ofOpSem ordinary) := ⟨State.pick, State.pick_valid⟩
  raw.guard (State.supported profile ·)

/-- A missing entry returns `none`. The bounded execution reports stops and exhaustion. -/
@[expose] def run (profile : Profile) (body : Body) (fuel : Nat) : Option (Bounded State Completion) :=
  (body.start? profile).map fun source => (oracle profile).run source fuel

theorem run_sound (initial : (model profile).initial body source) :
    ∃ result, run profile body fuel = some result ∧ result.Sound (semantics profile) source fuel := by
  exact ⟨_, by simp [run, Body.start_iff.mpr initial], (oracle profile).run_sound source fuel⟩

theorem run_exact (supported : source.supported profile) (enough : source.budget ≤ fuel) :
    (oracle profile).run source fuel =
      .stop (.finished source.result) (.observed (.returned source.result)) :=
  Proofs.Languages.Python.Core.run_exact (oracle profile) (Proofs.Languages.Python.Core.pick_known profile)
    supported enough

end Silmaril.Languages.Python.Core
