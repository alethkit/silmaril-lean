module

public import Silmaril.Logic.Temporal.TLA.Elaborator.Defs
public import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs

/-! # Import TLA+ state predicates, raw steps and temporal formulas from source -/

public section

namespace Silmaril.Logic.Temporal.TLA.Import

/-- Sorts for exactly the flexible variables, attested standard library
identities, and the names of the two nullary Boolean operators to select. -/
structure Profile where
  signature : Elaborator.Signature
  libraries : List Elaborator.StandardModule
  initial : Surface.Ident
  step : Surface.Ident

/-- Profile for Quint exports using Apalache 0.62.4. The caller attests that
the imported names resolve to those pinned libraries. -/
@[expose] def Profile.quintApalache0624 (signature : Elaborator.Signature) : Profile where
  signature := signature
  libraries := [.integers, .sequences, .finiteSets, .tlc, .apalache, .variants]
  initial := "q_init"
  step := "q_step"

/-- Each stage preserves its diagnostic, including parser source spans and
elaboration context on definition bodies. -/
inductive Diagnostic where
  | parse (cause : Surface.Parser.Diagnostic)
  | elaborate (cause : Elaborator.Diagnostic)
  | initial (name : Surface.Ident) (cause : Elaborator.Diagnostic)
  | step (name : Surface.Ident) (cause : Elaborator.Diagnostic)
  | temporal (name : Surface.Ident) (cause : Elaborator.Diagnostic)

/-- Use `initial.toStatePred` and `step.toAction` for the General TLA
denotations and `profile.signature.noRigid` for the outer rigid environment. -/
structure StateAction (signature : Elaborator.Signature) where
  initial : Kernel.StatePredicate signature.scope
  step : Kernel.StepPredicate signature.scope

private def checkModule (signature : Elaborator.Signature)
    (libraries : List Elaborator.StandardModule) (source : String) :
    Except Diagnostic (Elaborator.CheckedModule signature) := do
  let parsed ← (Surface.Parser.parseModule source).mapError .parse
  (Elaborator.elaborate libraries signature parsed).mapError .elaborate

/-- Parse the entire module and check all declarations before selecting the
initial predicate and raw step. `:=` has the pinned Apalache equality meaning
when imported. A client can add a bracket explicitly with `step.bracket`. -/
def importModule (profile : Profile) (source : String) :
    Except Diagnostic (StateAction profile.signature) := do
  let checked ← checkModule profile.signature profile.libraries source
  let initial ← (checked.statePredicate profile.initial).mapError (.initial profile.initial)
  let step ← (checked.stepPredicate profile.step).mapError (.step profile.step)
  return ⟨initial, step⟩

/-- Parse and check the entire module, then select a named temporal operator.
Call `toFormula signature.noRigid` on the result for its TLA semantics. -/
def importTemporal (signature : Elaborator.Signature) (libraries : List Elaborator.StandardModule)
    (name : Surface.Ident) (source : String) :
    Except Diagnostic (Elaborator.TemporalFormula signature.scope) := do
  let checked ← checkModule signature libraries source
  (checked.temporalFormula name).mapError (.temporal name)

end Silmaril.Logic.Temporal.TLA.Import
