module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Leaf.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Wrapper.Thms
public import Silmaril.Languages.Starlark.Lists.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Leaf

open Silmaril.Languages.Starlark.Modules (Catalog Source Executes Published enter finish restoreThread globalValues)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Wrapper (ReachedPrefix)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Leaf
open Silmaril.Languages.Starlark.Modules.Resolve.Block (ModuleBinders)
open Silmaril.Languages.Starlark.Lists (State freezes_iff_freeze)
open Silmaril.Languages.Starlark.Functions (Program restoreCaller)

local notation "Value" => Silmaril.Languages.Starlark.Lists.Value
local notation "ModuleResult" => Silmaril.Languages.Starlark.Modules.Result

private theorem collected {state : State} {names : List String} {values : List (String × Value)}
    (observed : Globals state names values) (source : Source) (declared : source.globals = names) :
    globalValues source state = values := by
  unfold globalValues
  rw [declared]
  clear declared
  induction observed with
  | nil => rfl
  | @initialized name names value rest read _ ih =>
    rw [List.filterMap_cons, show (state.bindingValue (Silmaril.Languages.Starlark.Modules.globalSlot name)).toOption.map
      (fun result => (name, result)) = some (name, value) by rw [read]; rfl]
    change (name, value) :: _ = _
    rw [ih]
  | @absent name names error rest read _ ih =>
    rw [List.filterMap_cons, show (state.bindingValue (Silmaril.Languages.Starlark.Modules.globalSlot name)).toOption.map
      (fun result => (name, result)) = none by rw [read]; rfl]
    exact ih

theorem finish_eq {source : Source} {names : List String} {caller : State}
    {out : ModuleResult Unit} {published : ModuleResult Published}
    (declared : source.globals = names) (finishes : Finishes names caller out published) :
    finish source caller out = published := by
  cases finishes with
  | failed => cases caller; rfl
  | published globals frozen =>
    have values := collected globals source declared
    have heap := (freezes_iff_freeze _ _ _).mp frozen
    simp [finish, Silmaril.Languages.Starlark.Modules.publish, values, restoreThread, restoreCaller,
      Silmaril.Languages.Starlark.Lists.State.freeze, List.filterMap_map, heap]

theorem module_observes {commands : List Command} {globals : List String} {linked : Program}
    {resolved : ResolvedModule} {step : Nat → State → Command → ModuleResult Unit → Prop}
    {out : ModuleResult Unit} {published : ModuleResult Published}
    (declared : ModuleBinders commands globals) (checked : resolve commands linked = .ok resolved)
    (host : Catalog) (caller : State)
    (sound : ∀ index state command out, step index state command out →
      ∃ code, resolved.source.commands[index]? = some code ∧ Executes resolved.program host state code out)
    (reached : ReachedPrefix step 0 (enter resolved.source caller) commands out)
    (observes : Finishes globals caller out published) :
    Initializes commands host caller linked (.ok published) ∧ runModule commands host caller linked = .ok published := by
  have agreement := Wrapper.checked_finish checked host caller sound reached
  rwa [finish_eq (Entry.checked_module_globals declared checked) observes] at agreement

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Leaf
