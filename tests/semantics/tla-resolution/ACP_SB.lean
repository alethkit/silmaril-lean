module

import Silmaril.Logic.Temporal.TLA.Resolution.Instances.Defs
meta import Silmaril.Logic.Temporal.TLA.Resolution.Instances.Defs
import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs
meta import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs

/-! Whole-source regression for the pinned ACP_SB fixture. See
`docs/projects/tla-acp-sb-resolution.md` for the byte pin and invocation. -/

open Silmaril.Logic.Temporal.TLA Resolution

private def expected : List (Surface.Ident × Levels.Level) :=
  (["TypeInvParticipant", "TypeInvCoordinator", "TypeInv",
    "InitParticipant", "InitCoordinator", "Init"].map (·, .state)) ++
  (["request", "getVote", "detectFault", "makeDecision", "coordBroadcast", "coordDie",
    "sendVote", "abortOnVote", "abortOnTimeoutRequest", "decide", "parDie", "parProg",
    "parProgN", "coordProgA", "coordProgB", "coordProgN", "progN"].map (·, .action)) ++
  (["fairness", "Spec", "AC1", "AC2", "AC3_1", "AC4", "AC3_2", "FaultyStable", "VoteStable",
    "StrongerAC2", "StrongerAC3_1", "NoRecovery", "DecisionReachedNoFault",
    "AbortImpliesNoVote", "AC5"].map (·, .temporal))

private def fromResult {α ε : Type} [Repr ε] : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

public def main (args : List String) : IO Unit := do
  let [file] := args | throw (IO.userError "expected the path to the pinned ACP_SB.tla")
  let source ← fromResult (Surface.Parser.parseModule (← IO.FS.readFile file))
  let root := "pinned/acp-sb"
  let input : Registry := [(root, .parsed source [])]
  let checked ← fromResult (Instances.check input root)
  let some resolved := checked.registry.moduleAt root | throw (IO.userError "missing ACP_SB")
  let some retained := resolved.source | throw (IO.userError "missing original Surface module")
  unless source.name = "ACP_SB" && source.extendsModules.isEmpty && source.units.length = 40 &&
      reprStr retained = reprStr source do
    throw (IO.userError "expected all ACP_SB units in the retained source")
  let actual ← source.units.zipIdx.filterMapM fun (unit, index) => do
    let .definition (.operator _ (.ident name _) _) := unit | return none
    let bindingSite : Site := ⟨root, [.unit index]⟩
    let some binding := resolved.bindingAt (.ident name)
      | throw (IO.userError s!"missing binding for {name}")
    let some term := checked.levels.expressionAt (bindingSite.child .body)
      | throw (IO.userError s!"missing body level for {name}")
    let some summary := checked.levels.operatorAt binding.id
      | throw (IO.userError s!"missing operator summary for {name}")
    unless binding.id = .declared bindingSite && summary.result = term do
      throw (IO.userError s!"mismatched source identity or summary for {name}")
    return some (name, term.floor)
  unless actual = expected do
    throw (IO.userError s!"unexpected definition names or levels: {reprStr actual}")
  IO.println "ACP_SB: all 40 units retained, all 38 operator levels match"
