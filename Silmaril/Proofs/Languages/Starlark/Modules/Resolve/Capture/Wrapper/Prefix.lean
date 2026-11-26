module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Wrapper.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall.Thms
public import Silmaril.Languages.Starlark.Modules.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Wrapper

open Silmaril.Languages.Starlark.Modules (Catalog Executes Runs Result enter finish)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Wrapper
open Silmaril.Languages.Starlark.Lists (State)
open Silmaril.Languages.Starlark.Functions (Program)

local notation "ModuleCommand" => Silmaril.Languages.Starlark.Modules.Command

private theorem drop_command (code : List ModuleCommand) {index : Nat} {command : ModuleCommand}
    (atIndex : code[index]? = some command) : code.drop index = command :: code.drop (index + 1) := by
  obtain ⟨within, equal⟩ := List.getElem?_eq_some_iff.mp atIndex
  rw [List.drop_eq_getElem_cons within, equal]

theorem prefix_sound {SourceCommand : Type}
    {step : Nat → State → SourceCommand → Result Unit → Prop}
    (program : Program) (host : Catalog) (code : List ModuleCommand)
    (sound : ∀ index state command out, step index state command out →
      ∃ compiled, code[index]? = some compiled ∧ Executes program host state compiled out)
    {index : Nat} {state : State} {source : List SourceCommand} {out : Result Unit}
    (reached : ReachedPrefix step index state source out) :
    Runs program host state ((code.drop index).take source.length) out := by
  induction reached with
  | nil => exact .done
  | next first _ ih =>
    obtain ⟨compiled, atIndex, ran⟩ := sound _ _ _ _ first
    rw [drop_command code atIndex]
    exact .step ran ih
  | error failed =>
    obtain ⟨compiled, atIndex, ran⟩ := sound _ _ _ _ failed
    rw [drop_command code atIndex]
    exact .failed ran

theorem checked_finish {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    {step : Nat → State → Command → Result Unit → Prop}
    (checked : resolve commands linked = .ok resolved) (host : Catalog) (caller : State)
    (sound : ∀ index state command out, step index state command out →
      ∃ compiled, resolved.source.commands[index]? = some compiled ∧
        Executes resolved.program host state compiled out)
    {out : Result Unit} (reached : ReachedPrefix step 0 (enter resolved.source caller) commands out) :
    Initializes commands host caller linked (.ok (finish resolved.source caller out)) ∧
      runModule commands host caller linked = .ok (finish resolved.source caller out) := by
  have ran := prefix_sound resolved.program host resolved.source.commands sound reached
  have count := Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall.checked_command_count checked
  have complete : Runs resolved.program host (enter resolved.source caller) resolved.source.commands out := by
    simpa [← count] using ran
  have init := Initializes.run checked (.run (checked_of_resolve checked).2.2.2 complete)
  exact ⟨init, (initializes_iff_runModule _ _ _ _ _).mp init⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Wrapper
