module

public import Silmaril.Languages.Starlark.Modules.Resolve.Operational.Defs
public import Silmaril.Languages.Starlark.Modules.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve

open Silmaril.Languages.Starlark.Modules (Catalog Published validateSource initializeModule)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Functions (Program)
open Silmaril.Languages.Starlark.Lists (State)

theorem checked_of_resolve {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (h : resolve commands linked = .ok resolved) :
    elaborateCommands commands linked = .ok (resolved.source.commands, resolved.program) ∧
      resolved.source.globals = globalNames commands ∧ resolved.source.temporaryNames = [] ∧
      validateSource resolved.program resolved.source = .ok () := by
  unfold resolve at h
  split at h
  · contradiction
  rename_i code program elaborated
  dsimp only at h
  split at h
  · contradiction
  rename_i checked
  cases h
  exact ⟨elaborated, rfl, rfl, checked⟩

theorem eq_runModule_of_initializes {commands : List Command} {host : Catalog} {caller : State}
    {linked : Program} {out : Result} (h : Initializes commands host caller linked out) :
    runModule commands host caller linked = out := by
  cases h with
  | reject failure => simp [runModule, failure]
  | run elaborated ran =>
    have evaluated := (Silmaril.Languages.Starlark.Modules.initializes_iff_initialize _ _ _ _ _).mp ran
    simp [runModule, elaborated, evaluated]

theorem initializes_runModule (commands : List Command) (host : Catalog) (caller : State) (linked : Program) :
    Initializes commands host caller linked (runModule commands host caller linked) := by
  cases h : resolve commands linked with
  | error error => simpa [runModule, h] using (Initializes.reject (host := host) (caller := caller) h)
  | ok resolved =>
    have initialized := (Silmaril.Languages.Starlark.Modules.initializes_iff_initialize
      resolved.program host resolved.source caller _).mpr rfl
    simpa [runModule, h] using (Initializes.run h initialized)

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve
