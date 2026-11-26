module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Exit.Thms

import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Exit.Inversion.Execution

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Exit.Inversion

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame Opcode packValues)
open Silmaril.Machine.RTL.SSA (StepsNWithin toLambdaSSA)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg model)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (evalOp)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

variable {old new tests : Nat} {entrySigs sigs : List (List PortTy)}
variable {mapping : InputMap old new} {source : Family.Source old old entrySigs sigs tests}
variable {origins : List (HeaderWord new old sigs)}

/-- Invert a terminating CF run from a matched header into positional feedbacks and the first taken exit. -/
theorem from_header (compiled : Compiled mapping source origins) (input : WordTuple new) (mem : Memory)
    (fuel : Nat) (value : Word) (carried : WordTuple old) (before : Frame Reg)
    (matched : ArgsMatch before (appendTuple carried input))
    (observed : compiled.setup.cf.runFrom evalOp fuel (wordEnv input) (headerFrame _ _ carried) =
      some (.cons value .nil)) :
    ∃ slots finish after,
      source.ReturnsAlong (mapping.pull input) slots carried value ∧
      Realized compiled.setup input mem slots carried before finish after ∧
      Taken compiled input mem finish after value ∧ cfCost slots + 2 ≤ fuel :=
  Proofs.from_header compiled input mem fuel value carried before matched observed

/-- Derive the initial RTL frame match from the checked entry and recover the reached CF, RTL and explicit-Φ cuts. -/
theorem from_entry (compiled : Compiled mapping source origins) (input : WordTuple new) (mem : Memory)
    (fuel : Nat) (value : Word)
    (observed : compiled.setup.cf.run evalOp fuel (wordEnv input) = some (.cons value .nil)) :
    let initial := source.primary.initial model (mapping.pull input)
    ∃ slots finish before after,
      compiled.rtl.start 0 (words input) mem =
        some ⟨⟨0, 0, 0⟩, bindWords 0 Frame.empty input, [], mem⟩ ∧
      StepsNWithin compiled.rtl [] (entrySigs.length + 1)
        ⟨⟨0, 0, 0⟩, bindWords 0 Frame.empty input, [], mem⟩ ⟨⟨0, 1, 0⟩, before, [], mem⟩ ∧
      source.ReturnsAlong (mapping.pull input) slots initial value ∧
      Realized compiled.setup input mem slots initial before finish after ∧
      Taken compiled input mem finish after value ∧ cfCost slots + 2 + 1 ≤ fuel :=
  Proofs.from_entry compiled input mem fuel value observed

/-- Reflect an actual CF return into bounded RTL and the canonical typed λSSA exit, with all memory preserved. -/
theorem reflect (compiled : Compiled mapping source origins) (input : WordTuple new) (mem : Memory)
    (fuel : Nat) (value : Word)
    (observed : compiled.setup.cf.run evalOp fuel (wordEnv input) = some (.cons value .nil))
    (env : Silmaril.Isotope.LambdaSSA.Semantics.Env Word) (entry : env 0 = packValues (words input)) :
    ∃ slots, source.ReturnsAlong (mapping.pull input) slots (source.primary.initial model (mapping.pull input)) value ∧
      cfCost slots + 2 + 1 ≤ fuel ∧
      compiled.rtl.runMain (entrySigs.length + 1 + (rtlCost sigs.length slots + (sigs.length + 2)))
        0 (words input) mem = .returned [value] mem ∧
      compiled.setup.cf.run evalOp (cfCost slots + 2 + 1) (wordEnv input) = some (.cons value .nil) ∧
      Eval (Opcode.step (sigs := [⟨new, 1⟩]) compiled.rtl.oracle) env
        (toLambdaSSA [⟨new, 1⟩] (lowerFunc (mapCaptures mapping source))) mem 0 (packValues [value]) mem :=
  Proofs.reflect compiled input mem fuel value observed env entry

/-- Recover the actual entry path, ordered Φ packets and first exit from an RTL
return. Both runners use the costs of the recovered path in their own units. -/
theorem from_rtl (compiled : Compiled mapping source origins) (input : WordTuple new)
    (initial final : Memory) (fuel : Nat) (returned : List Word)
    (observed : compiled.rtl.runMain fuel 0 (words input) initial = .returned returned final) :
    let bank := source.primary.initial model (mapping.pull input)
    ∃ slots value before finish after,
      returned = [value] ∧ final = initial ∧
      source.ReturnsAlong (mapping.pull input) slots bank value ∧
      rtlFuel entrySigs sigs slots ≤ fuel ∧
      compiled.rtl.start 0 (words input) initial =
        some ⟨⟨0, 0, 0⟩, bindWords 0 Frame.empty input, [], initial⟩ ∧
      StepsNWithin compiled.rtl [] (entrySigs.length + 1)
        ⟨⟨0, 0, 0⟩, bindWords 0 Frame.empty input, [], initial⟩ ⟨⟨0, 1, 0⟩, before, [], initial⟩ ∧
      Realized compiled.setup input initial slots bank before finish after ∧
      Taken compiled input initial finish after value ∧
      compiled.rtl.runMain (rtlFuel entrySigs sigs slots) 0 (words input) initial = .returned returned final ∧
      compiled.setup.cf.run evalOp (cfCost slots + 2 + 1) (wordEnv input) = some (.cons value .nil) :=
  Proofs.from_rtl compiled input initial final fuel returned observed

/-- Reflect an actual machine return to exit zero under the packed capture binding. -/
theorem region_of_rtl (compiled : Compiled mapping source origins) (input : WordTuple new)
    (initial final : Memory) (fuel : Nat) (returned : List Word)
    (observed : compiled.rtl.runMain fuel 0 (words input) initial = .returned returned final)
    (env : Silmaril.Isotope.LambdaSSA.Semantics.Env Word) (entry : env 0 = packValues (words input)) :
    Eval (Opcode.step (sigs := [⟨new, 1⟩]) compiled.rtl.oracle) env
      (toLambdaSSA [⟨new, 1⟩] (lowerFunc (mapCaptures mapping source))) initial 0 (packValues returned) final :=
  Proofs.region_of_rtl compiled input initial final fuel returned observed env entry

/-- A bounded RTL return exists exactly when an ordered dispatch route
(the positional Φ observations recorded by `Realized`) reaches a taken
exit with the same word. That single witness also supplies a matching
bounded CF return, with full memory preserved by both backends. This
consolidates the actual-run forward law (`Exit.returns`/`after_prefix`)
and its converse (`from_rtl`) into one public existence statement. -/
theorem returns_iff (compiled : Compiled mapping source origins) (input : WordTuple new) (mem : Memory)
    (value : Word) :
    (∃ fuel, compiled.rtl.runMain fuel 0 (words input) mem = .returned [value] mem) ↔
    ∃ slots before finish after,
      source.ReturnsAlong (mapping.pull input) slots (source.primary.initial model (mapping.pull input)) value ∧
      Realized compiled.setup input mem slots (source.primary.initial model (mapping.pull input)) before finish after ∧
      Taken compiled input mem finish after value ∧
      compiled.rtl.runMain (rtlFuel entrySigs sigs slots) 0 (words input) mem = .returned [value] mem ∧
      compiled.setup.cf.run evalOp (cfCost slots + 2 + 1) (wordEnv input) = some (.cons value .nil) :=
  Proofs.returns_iff compiled input mem value

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Exit.Inversion
