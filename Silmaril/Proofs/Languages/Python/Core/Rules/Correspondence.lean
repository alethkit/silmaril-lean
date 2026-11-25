module

public import Silmaril.Languages.Python.Core.Rules.Defs
public import Silmaril.Semantics.SOS.Thms

public section

namespace Silmaril.Proofs.Languages.Python.Core.Rules

open Silmaril.Languages.Python.Core Silmaril.Languages.Python.Core.Rules

private def native : Judgment → Prop
  | .primitive op left right result => op.Eval left right result
  | .expression source next => source.Step next
  | .edge source label target => Step source label target

private theorem native_closed : Silmaril.Semantics.SOS.Closed rules native := by
  intro rule member premises
  change Schema rule at member
  cases member with
  | add left right => exact .add left right
  | div left right nonzero => exact .div left right nonzero
  | divZero left => exact .divZero left
  | left _ left _ next => exact Expr.Step.left (premises (.expression left next) (by simp))
  | right _ _ right next => exact Expr.Step.right (premises (.expression right next) (by simp))
  | compute op left right result =>
    exact Expr.Step.compute (premises (.primitive op left right result) (by simp))
  | evalValue source next => exact Step.expr (premises (.expression source (.ok next)) (by simp))
  | evalError source error => exact Step.expr (premises (.expression source (.error error)) (by simp))
  | ret value => exact .ret value
  | raise error => exact .raise error

private theorem derive_fact {judgment : Judgment} (schema : Schema ⟨[], judgment⟩) :
    Derives judgment :=
  .apply schema (fun _ absent => nomatch absent)

private theorem derive_premise {premise conclusion : Judgment}
    (schema : Schema ⟨[premise], conclusion⟩) (proof : Derives premise) : Derives conclusion :=
  .apply schema fun _ member => (List.mem_singleton.mp member).symm ▸ proof

private theorem derive_primitive {op : BinOp} {left right : Int} {result : Completion}
    (eval : op.Eval left right result) : Derives (.primitive op left right result) := by
  cases eval with
  | add left right => exact derive_fact (.add left right)
  | div left right nonzero => exact derive_fact (.div left right nonzero)
  | divZero left => exact derive_fact (.divZero left)

private theorem derive_expression {source : Expr} {next : Except Exception Expr}
    (step : source.Step next) : Derives (.expression source next) := by
  induction step with
  | left _ derived => exact derive_premise (.left ..) derived
  | right _ derived => exact derive_premise (.right ..) derived
  | compute eval => exact derive_premise (.compute ..) (derive_primitive eval)

private theorem derive_step {source target : State} {label : Option Completion}
    (step : Step source label target) : Derives (.edge source label target) := by
  cases step with
  | @expr expr next step =>
    cases next with
    | ok expr' => exact derive_premise (.evalValue expr expr') (derive_expression step)
    | error error => exact derive_premise (.evalError expr error) (derive_expression step)
  | ret value => exact derive_fact (.ret value)
  | raise error => exact derive_fact (.raise error)

theorem primitive_iff {op : BinOp} {left right : Int} {result : Completion} :
    Derives (.primitive op left right result) ↔ op.Eval left right result :=
  ⟨fun proof => proof.least native_closed, derive_primitive⟩

theorem expression_iff {source : Expr} {next : Except Exception Expr} :
    Derives (.expression source next) ↔ source.Step next :=
  ⟨fun proof => proof.least native_closed, derive_expression⟩

theorem step_iff {source target : State} {label : Option Completion} :
    Derives (.edge source label target) ↔ Step source label target :=
  ⟨fun proof => proof.least native_closed, derive_step⟩

end Silmaril.Proofs.Languages.Python.Core.Rules
