module

meta import Lean.Elab.Tactic.Cbv
public import Silmaril.Languages.Starlark.Frontend.Module.Thms
import all Silmaril.Languages.Starlark.Frontend.Module.Defs
import all Silmaril.Languages.Starlark.Frontend.Defs
import all Silmaril.Languages.Starlark.Frontend.Lexer.Defs
import all Silmaril.Languages.Starlark.Modules.Resolve.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs
meta import Silmaril.Languages.Starlark.Modules.Defs
import all Silmaril.Languages.Starlark.Functions.Lowering.Resolve.Defs
import all Silmaril.Languages.Starlark.Functions.Denotation.Defs
import all Silmaril.Languages.Starlark.Functions.Expressions.Denotation.Defs
import all Silmaril.Languages.Starlark.Lists.Denotation.Defs

namespace Silmaril.Languages.Starlark.Frontend.Module

public inductive Observation where
  | exportedInt (value : Int)
  | undefinedName (name : String)
  | missingArgument (name : String)
  deriving DecidableEq

public structure Control where
  name : String
  source : String
  expected : Observation

private def success := "# 雪\ndef id(x):\n  return x\nout = id(7)"
private def runtimeFailure := "# 雪\ndef id(x):\n  return x\nout = id()"
private def validationFailure := "def id(x):\n  return x\nout = id(missing)"
private def continuedCall :=
  "# choisit\r\ndef pick(flag, value):\r\n  if flag:\r\n    return value\r\n  else:\r\n    return 0\r\n" ++
  "_seed = 29\r\nout = pick(\r\n  False or True,\r\n  _seed if True else 1,\r\n)"

/-- Acceptance and observation controls shared with the pinned Go tool. -/
public def controls : List Control := [
  ⟨"text-module-export", success, .exportedInt 7⟩,
  ⟨"text-module-continuation", continuedCall, .exportedInt 29⟩,
  ⟨"text-module-missing-argument", runtimeFailure, .missingArgument "x"⟩,
  ⟨"text-module-undefined-name", validationFailure, .undefinedName "missing"⟩]

private def observe (source : String) : Option Observation :=
  match runUtf8 source.toUTF8 with
  | .ok (.ok published _) =>
    match published.exports.lookup "out" with
    | some (.scalar (.int value)) => some (.exportedInt value)
    | _ => none
  | .ok (.error (.runtime (.missingArguments [name])) _) => some (.missingArgument name)
  | .error (.validation (.expression (.lexical (.undefinedName name)))) => some (.undefinedName name)
  | _ => none

section

set_option maxRecDepth 6000
set_option maxHeartbeats 2000000

-- Use the resolver's equations during proof reduction to keep the executable
-- well-founded recursion from expanding inside the kernel.
private theorem readExpr_eq (context : Functions.Lowering.Resolve.Context)
    (expr : Functions.Lowering.Resolve.SourceExpr) :
    Modules.Resolve.readExpr context expr = monadLift
      ((Functions.Lowering.Resolve.resolveTracked context expr).mapError Modules.Resolve.Error.expression) := rfl

private theorem startsWith_eq_prefix (source pattern : String) :
    source.startsWith pattern = pattern.toList.isPrefixOf source.toList :=
  Bool.eq_iff_iff.mpr (String.startsWith_string_iff.trans List.isPrefixOf_iff_prefix.symm)

attribute [local cbv_eval] Modules.Resolve.compileBody.eq_def readExpr_eq startsWith_eq_prefix

-- Reduce through actual UTF-8 parsing, normalization, checked resolution, and publication.
example : observe success = some (.exportedInt 7) := by cbv
example : observe runtimeFailure = some (.missingArgument "x") := by cbv
example : observe validationFailure = some (.undefinedName "missing") := by cbv

end

#guard controls.all fun control => decide (observe control.source = some control.expected)

private def exportNames (source : String) : Option (List String) :=
  match runUtf8 source.toUTF8 with
  | .ok (.ok published _) => some (published.exports.map Prod.fst)
  | _ => none

#guard decide (exportNames continuedCall = some ["pick", "out"])

private def commandSpans (source : String) : Option (List Span) := do
  let parsed ← (parseUtf8 source.toUTF8).toOption
  return parsed.commands.map LocatedCommand.span

example : commandSpans success = some [⟨⟨6, 2, 1⟩, ⟨27, 3, 11⟩⟩, ⟨⟨28, 4, 1⟩, ⟨39, 4, 12⟩⟩] :=
  by decide +kernel

private def frontendDiagnostic (source : String) : Option Diagnostic :=
  match runUtf8 source.toUTF8 with
  | .error (.frontend diagnostic) => some diagnostic
  | _ => none

example : frontendDiagnostic "out = f(1 + 2)" =
    some ⟨.unsupported .operator, ⟨⟨8, 1, 9⟩, ⟨13, 1, 14⟩⟩⟩ := by decide +kernel

example : frontendDiagnostic "out = f(x=7)" =
    some ⟨.unsupported .callArguments, ⟨⟨9, 1, 10⟩, ⟨10, 1, 11⟩⟩⟩ := by decide +kernel

example : frontendDiagnostic "out = f(1=7)" =
    some ⟨.expected "',' or ')'", ⟨⟨9, 1, 10⟩, ⟨10, 1, 11⟩⟩⟩ := by decide +kernel

example : frontendDiagnostic "out = f(,7)" =
    some ⟨.expected "an expression", ⟨⟨8, 1, 9⟩, ⟨9, 1, 10⟩⟩⟩ := by decide +kernel

end Silmaril.Languages.Starlark.Frontend.Module
