module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Defs
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Producer
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Consumer
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Entry.Thms
import Silmaril.Languages.Starlark.Modules.Loader.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Modules (enter fileSlot globalSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
open Silmaril.Languages.Starlark.Functions (Program)
open Silmaril.Languages.Starlark.Lists (State)
open Silmaril.Languages.Starlark.Modules.Loader (Session)

private theorem consumer_agrees {commands : List Modules.Resolve.Command}
    {producer consumer : ResolvedModule} {exports : Environment} (plan : Consumer)
    (checked : resolve plan.commands producer.program = .ok consumer)
    (covered : Covered exports commands plan) (caller : Session)
    (uncached : caller.cache.lookup 1 = none)
    {dependency : Modules.Loader.Result Modules.Published}
    (sourceDependency : Producer commands producer.source
      {caller with runtime := enter consumer.source caller.runtime} dependency)
    (nativeDependency : Modules.Loader.Runs producer.program (graph producer consumer plan) [1] (.initialize 0)
      {caller with runtime := enter consumer.source caller.runtime} dependency)
    (slots : (reachedSession dependency).runtime.slots = (enter consumer.source caller.runtime).slots)
    (kept : KeepsContents (enter consumer.source caller.runtime) (reachedSession dependency).runtime)
    (success : ∀ publication reached, dependency = .ok publication reached →
      PublishedLive exports producer.program publication reached.runtime ∧
      ∀ name value, publication.exports.lookup name = some value → name ∈ Trace.names commands) :
    Agrees commands producer consumer plan exports caller := by
  obtain ⟨same, code, _, files⟩ := consumer_layout plan checked
  have valid : Modules.validateSource producer.program consumer.source = .ok () :=
    same ▸ (checked_of_resolve checked).2.2.2
  have label : Modules.Loader.resolve (graph producer consumer plan) 1 plan.label = some 0 := by
    simp [Modules.Loader.resolve, graph]
  have complete (out : Modules.Loader.Result Unit)
      (ran : Modules.Loader.Runs producer.program (graph producer consumer plan) [1] (.commands 1 plan.code)
        {caller with runtime := enter consumer.source caller.runtime} out) :
      Modules.Loader.Runs producer.program (graph producer consumer plan) [] (.initialize 1) caller
        (Modules.Loader.finish 1 consumer.source caller.runtime out) := by
    apply Modules.Loader.Runs.initialize (by simp [graph]) (by simp) uncached valid
    change Modules.Loader.Runs producer.program (graph producer consumer plan) [1]
      (.commands 1 consumer.source.commands) {caller with runtime := enter consumer.source caller.runtime} out
    rw [code]
    exact ran
  cases dependency with
  | error error reached =>
    have native := complete _ (.failed (.loadFailed label nativeDependency))
    exact ⟨_, .producerError sourceDependency, native,
      (Modules.Loader.runs_iff_denote _ _ _ _ _ _).mp native⟩
  | ok published reached =>
    obtain ⟨live, declared⟩ := success published reached rfl
    have runImport {out : Modules.Result Unit}
        (independent : BindsAlias plan published reached.runtime out) :
        Modules.Loader.Runs producer.program (graph producer consumer plan) [1] (.command 1 (.load plan.label [plan.item]))
          {caller with runtime := enter consumer.source caller.runtime} (Modules.Loader.liftResult 1 reached out) := by
      rw [← import_agrees independent]
      exact .load label nativeDependency
    cases tracked : exports plan.name with
    | none =>
      have absent : plan.name ∉ Trace.names commands := covered.resolve_left (by simp [tracked])
      have missing : published.exports.lookup plan.name = none := by
        cases seen : published.exports.lookup plan.name with
        | none => rfl
        | some value => exact (absent (declared _ value seen)).elim
      have independent := BindsAlias.missing (plan := plan) (state := reached.runtime) missing
      have native := complete _ (.failed (runImport independent))
      exact ⟨_, .missing sourceDependency independent, native,
        (Modules.Loader.runs_iff_denote _ _ _ _ _ _).mp native⟩
    | some callee =>
      obtain ⟨linked, address, defining, loaded, record, _⟩ := live plan.name callee tracked plan.publicName
      obtain ⟨aliasCell, owned, blank⟩ := Entry.entered_blank consumer.source caller.runtime (fileSlot plan.alias)
        (by simp [files])
      obtain ⟨flag, preserved⟩ := kept _ _ blank
      obtain ⟨read, ⟨closure⟩⟩ := reached_alias (plan := plan) (slots.symm ▸ owned) preserved record
      let bound := reached.runtime.write (fileSlot plan.alias) (.function address)
      have independent := BindsAlias.found (plan := plan) (state := reached.runtime) loaded
      obtain ⟨out, tail, nativeTail⟩ := tail_reached (manifest := graph producer consumer plan)
        (s := {reached with runtime := bound}) checked same callee linked read closure
      have native := complete _ (.step (runImport independent) nativeTail)
      rw [← observed_eq (before := {reached with runtime := bound})] at native
      exact ⟨_, .called sourceDependency independent tracked tail, native,
        (Modules.Loader.runs_iff_denote _ _ _ _ _ _).mp native⟩

theorem cold_agrees {commands : List Modules.Resolve.Command} {linked final : Program}
    {code : List Modules.Command} {producer consumer : ResolvedModule} {exports : Environment}
    (profile : Plan (Trace.names commands) (fun _ => none) commands linked code final exports)
    (producerChecked : resolve commands linked = .ok producer)
    (plan : Consumer) (consumerChecked : resolve plan.commands producer.program = .ok consumer)
    (covered : Covered exports commands plan) (caller : State) :
    Agrees commands producer consumer plan exports ⟨caller, []⟩ := by
  obtain ⟨_, source, native, slots, kept, ready⟩ := producer_cold (consumer := consumer)
    profile producerChecked plan [1] (by decide) ⟨enter consumer.source caller, []⟩ rfl
  exact consumer_agrees plan consumerChecked covered ⟨caller, []⟩ rfl source native slots kept
    (fun _ _ success => (ready _ _ success).2)

theorem preloaded_agrees {commands : List Modules.Resolve.Command} {linked final : Program}
    {code : List Modules.Command} {producer consumer : ResolvedModule} {exports : Environment}
    (profile : Plan (Trace.names commands) (fun _ => none) commands linked code final exports)
    (producerChecked : resolve commands linked = .ok producer)
    (plan : Consumer) (consumerChecked : resolve plan.commands producer.program = .ok consumer)
    (covered : Covered exports commands plan) (caller : State) :
    ∃ preload, Producer commands producer.source ⟨caller, []⟩ preload ∧
      Modules.Loader.load producer.program (graph producer consumer plan) 0 ⟨caller, []⟩ = preload ∧
      ∀ published reached, preload = .ok published reached →
        reached.cache = [(0, published)] ∧ Agrees commands producer consumer plan exports reached := by
  obtain ⟨out, source, native, _, _, ready⟩ := producer_cold (consumer := consumer)
    profile producerChecked plan [] (by decide) ⟨caller, []⟩ rfl
  refine ⟨out, source, (Modules.Loader.runs_iff_denote _ _ _ _ _ _).mp native, ?_⟩
  intro published reached successful
  obtain ⟨cache, live, declared⟩ := ready _ _ successful
  let entered := { reached with runtime := enter consumer.source reached.runtime }
  have hit : entered.cache.lookup 0 = some published := by simp [entered, cache]
  have cachedSource : Producer commands producer.source entered (.ok published entered) := .cached hit
  have cachedNative : Modules.Loader.Runs producer.program (graph producer consumer plan) [1] (.initialize 0)
      entered (.ok published entered) := .cached (by decide) hit
  refine ⟨cache, consumer_agrees plan consumerChecked covered reached (by simp [cache])
    cachedSource cachedNative rfl (fun _ cell found => ⟨cell.frozen, found⟩) ?_⟩
  intro value final same
  cases same
  exact ⟨cached_publication live (Entry.entered_cells consumer.source reached.runtime).2, declared⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
