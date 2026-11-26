module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain.Defs
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain.Publication
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Invariant
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Frame
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Modules (fileSlot)
open Silmaril.Languages.Starlark.Modules.Loader (Manifest ModuleId Session)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain
open Silmaril.Languages.Starlark.Functions (Program)
open Silmaril.Languages.Starlark.Lists (Cell State)
local notation "ImportFrame" => Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Frame

@[expose] def KeepsBelow (floor : Nat) (before after : State) : Prop :=
  ∀ address cell, address < floor → before.heap[address]? = some cell →
    ∃ flag, after.heap[address]? = some {cell with frozen := flag}

theorem below_trans {floor : Nat} {before middle after : State}
    (first : KeepsBelow floor before middle) (second : KeepsBelow floor middle after) :
    KeepsBelow floor before after := by
  intro address cell small found
  obtain ⟨flag, stored⟩ := first address cell small found
  exact second address {cell with frozen := flag} small stored

private theorem blank_after {before after : State} {binding : Binding}
    (slots : after.slots = before.slots) (contents : KeepsContents before after)
    (blank : Blank before binding) : Blank after binding := by
  obtain ⟨address, flag, owned, stored⟩ := blank
  obtain ⟨frozen, next⟩ := contents address ⟨.binding none, flag⟩ stored
  exact ⟨address, frozen, slots ▸ owned, next⟩

private theorem frame_after {aliases globals : List String} {before after : State}
    (slots : after.slots = before.slots) (contents : KeepsContents before after)
    (frame : ImportFrame aliases globals before) : ImportFrame aliases globals after := by
  refine ⟨?_, ?_⟩
  · intro first second address atFirst atSecond
    exact frame.1 _ _ _ (slots.symm ▸ atFirst) (slots.symm ▸ atSecond)
  ·
    intro binding member
    obtain ⟨address, value, flag, owned, stored⟩ := frame.2 binding member
    obtain ⟨frozen, next⟩ := contents address ⟨.binding value, flag⟩ stored
    exact ⟨address, value, frozen, slots ▸ owned, next⟩

private theorem live_after {aliases : List String} {origin program : Program} {env : Tracked} {before after : State}
    (slots : after.slots = before.slots) (contents : KeepsContents before after)
    (live : Live aliases origin program env before) : Live aliases origin program env after := by
  intro name callee tracked
  obtain ⟨slot, address, flag, owned, stored, record⟩ := live name callee tracked
  obtain ⟨frozen, next⟩ := contents slot ⟨.binding (some (.function address)), flag⟩ stored
  exact ⟨slot, address, frozen, slots ▸ owned, next, transport_callable record (closure_cells_of_contents contents)⟩

/-- The reached prefix keeps previously published modules and protects cells
outside the importer frame. Success establishes the suite's entry invariant. -/
structure PrefixReached (origin program : Program) (manifest : Manifest) (exports : ModuleId → Tracked)
    (aliases globals : List String) (floor : Nat) (reserved : List Binding) (final : Option Tracked)
    (caller : Session) (out : Modules.Loader.Result Unit) : Prop where
  slots : (resultSession out).runtime.slots = caller.runtime.slots
  contents : KeepsBelow floor caller.runtime (resultSession out).runtime
  cache : Cache origin program manifest exports (resultSession out)
  retained : ∀ id value, caller.cache.lookup id = some value → (resultSession out).cache.lookup id = some value
  ready : ∀ next, out = .ok () next →
    ∃ env, final = some env ∧ ImportFrame aliases globals next.runtime ∧ Live aliases origin program env next.runtime ∧
      ∀ binding ∈ reserved, Blank next.runtime binding

/-- The continuation receives only a successful prefix. An error leaves the
remaining load commands and any body suffix unreachable. -/
@[expose] def Continues (program : Program) (manifest : Manifest) (active : List ModuleId) (id : ModuleId)
    (suffix : List Modules.Command) (prefixOut out : Modules.Loader.Result Unit) : Prop :=
  match prefixOut with
  | .ok () reached => Modules.Loader.Runs program manifest active (.commands id suffix) reached out
  | .error error reached => out = .error error reached

theorem run_prefix {origin program : Program} {manifest : Manifest} {exports : ModuleId → Tracked}
    {id : ModuleId} {bound : id < manifest.size} {active : List ModuleId}
    (loadEarlier : ∀ dependency, dependency < id → ∀ session,
      Cache origin program manifest exports session →
      ∃ out, TraceRun manifest dependency session out ∧
        Modules.Loader.Runs program manifest active (.initialize dependency) session out ∧
        Reached origin program manifest exports dependency session out)
    {imports : List ImportSite} {env : Tracked} {final : Option Tracked}
    (plan : ImportPlan manifest exports id bound imports env final)
    {aliases globals : List String} {floor : Nat} {reserved : List Binding}
    (visible : ∀ site ∈ imports, site.alias ∈ aliases)
    (unique : (imports.map ImportSite.alias).Nodup)
    (disjoint : ∀ site ∈ imports, fileSlot site.alias ∉ reserved)
    (caller : Session) (cache : Cache origin program manifest exports caller)
    (frame : ImportFrame aliases globals caller.runtime) (fresh : FreshSlots floor caller.runtime)
    (live : Live aliases origin program env caller.runtime)
    (pending : ∀ site ∈ imports, Blank caller.runtime (fileSlot site.alias))
    (untouched : ∀ binding ∈ reserved, Blank caller.runtime binding) :
    ∃ out, ImportTrace manifest id imports caller out ∧
      (∀ suffix result, Continues program manifest active id suffix out result →
        Modules.Loader.Runs program manifest active (.commands id (imports.map ImportSite.code ++ suffix)) caller result) ∧
      PrefixReached origin program manifest exports aliases globals floor reserved final caller out := by
  induction plan generalizing caller with
  | done env =>
    exact ⟨_, .done caller, fun _ _ rest => rest, ⟨rfl, fun _ cell _ stored => ⟨cell.frozen, stored⟩, cache,
      fun _ _ old => old, fun _ same => by cases same; exact ⟨env, rfl, frame, live, untouched⟩⟩⟩
  | unresolved label =>
    refine ⟨_, .unresolved label, ?_, ⟨rfl, fun _ cell _ stored => ⟨cell.frozen, stored⟩, cache,
      fun _ _ old => old, fun _ impossible => nomatch impossible⟩⟩
    intro suffix result rest
    cases rest
    exact .failed (.missingLabel label)
  | @missing site tail env dependency earlier label absent =>
    obtain ⟨loaded, trace, native, reached⟩ := loadEarlier dependency earlier caller cache
    cases loaded with
    | error error stopped =>
      refine ⟨_, .dependencyError label trace, ?_, ⟨reached.slots, fun _ _ _ => reached.contents _ _,
        reached.cache, reached.retained, fun _ impossible => nomatch impossible⟩⟩
      intro suffix result rest
      cases rest
      exact .failed (.loadFailed label native)
    | ok published stopped =>
      obtain ⟨_, actual⟩ := reached.cache dependency published (reached.published _ _ rfl)
      have missing : published.exports.lookup site.name = none := by
        cases found : published.exports.lookup site.name with
        | none => rfl
        | some value => exact (absent (actual.1 _ _ found)).elim
      refine ⟨_, .missing label trace missing, ?_, ⟨reached.slots, fun _ _ _ => reached.contents _ _,
        reached.cache, reached.retained, fun _ impossible => nomatch impossible⟩⟩
      intro suffix result rest
      cases rest
      apply Modules.Loader.Runs.failed
      have ran := Modules.Loader.Runs.load (imports := [site.item]) label native
      simpa [ImportSite.code, Modules.importsOf, Modules.bindImports, ImportSite.item, site.publicName, missing,
        Modules.Loader.liftResult, List.mapM_cons, bind, Except.bind, throw, throwThe, MonadExceptOf.throw,
        pure, Except.pure] using ran
  | @found site tail env dependency callee final earlier label tracked sourceTail ih =>
    obtain ⟨loaded, trace, native, reached⟩ := loadEarlier dependency earlier caller cache
    cases loaded with
    | error error stopped =>
      refine ⟨_, .dependencyError label trace, ?_, ⟨reached.slots, fun _ _ _ => reached.contents _ _,
        reached.cache, reached.retained, fun _ impossible => nomatch impossible⟩⟩
      intro suffix result rest
      cases rest
      exact .failed (.loadFailed label native)
    | ok published stopped =>
      obtain ⟨_, actual⟩ := reached.cache dependency published (reached.published _ _ rfl)
      obtain ⟨address, found, record⟩ := actual.2 site.name callee tracked site.publicName
      let value := Lists.Value.function address
      let bound := {stopped with runtime := stopped.runtime.write (fileSlot site.alias) value}
      have blank := blank_after reached.slots reached.contents (pending site List.mem_cons_self)
      have atAlias : readSlot aliases site.alias = fileSlot site.alias := by
        simp [readSlot, visible site List.mem_cons_self]
      have afterLive := live_after reached.slots reached.contents live
      have boundLive : Live aliases origin program (track env site.alias (some callee)) bound.runtime := by
        exact Eq.mp (congrArg (fun target => Live aliases origin program (track env site.alias (some callee))
          (stopped.runtime.write target value)) atAlias)
          (write_tracked (atAlias.symm ▸ blank) afterLive value (some callee)
            (fun target same => by cases same; exact ⟨address, rfl, record⟩))
      have boundSlots : bound.runtime.slots = caller.runtime.slots :=
        (write_slots _ _ _).trans reached.slots
      have distinct : RootCall.DistinctOwned stopped.runtime := (frame_after reached.slots reached.contents frame).1
      have pendingAfter (binding : Binding) (other : fileSlot site.alias ≠ binding) (before : Blank caller.runtime binding) :
          Blank bound.runtime binding :=
        other_blank distinct other (blank_after reached.slots reached.contents before) value
      have readyTail : ∀ next ∈ tail, Blank bound.runtime (fileSlot next.alias) := by
        intro next member
        apply pendingAfter _ _ (pending next (List.mem_cons_of_mem _ member))
        intro same
        have sameName : site.alias = next.alias := congrArg Binding.name same
        exact (List.nodup_cons.mp unique).1 (List.mem_map.mpr ⟨next, member, sameName.symm⟩)
      have boundCache := cache_transport (next := bound) reached.cache (write_blank_cells blank value) rfl
      have boundFrame := writes_frame (frame_after reached.slots reached.contents frame) (fileSlot site.alias) value
      obtain ⟨out, tailTrace, tailNative, after⟩ := ih
        (fun next member => visible next (List.mem_cons_of_mem _ member)) (List.nodup_cons.mp unique).2
        (fun next member => disjoint next (List.mem_cons_of_mem _ member)) bound boundCache boundFrame
        (fun binding slot owned => fresh binding slot (boundSlots ▸ owned)) boundLive readyTail
        (fun binding member => pendingAfter binding (fun same => disjoint site List.mem_cons_self (same ▸ member))
          (untouched binding member))
      have step : Modules.Loader.Runs program manifest active (.command id site.code) caller (.ok () bound) := by
        have ran := Modules.Loader.Runs.load (imports := [site.item]) label native
        simpa [ImportSite.code, Modules.importsOf, Modules.bindImports, ImportSite.item, site.publicName, found,
          Modules.Loader.liftResult, List.mapM_cons, bind, Except.bind, pure, Except.pure, bound, value] using ran
      obtain ⟨aliasCell, _, owned, _⟩ := blank
      have writeKeeps := write_keeps_below owned (fresh _ _ (reached.slots ▸ owned)) value
      have kept : KeepsBelow floor caller.runtime bound.runtime :=
        below_trans (fun _ _ _ => reached.contents _ _)
          (fun _ cell small stored => ⟨cell.frozen, writeKeeps.2 _ _ small stored⟩)
      refine ⟨out, .next label trace found tailTrace, fun suffix result rest => .step step (tailNative suffix result rest),
        ⟨after.slots.trans boundSlots, below_trans kept after.contents, after.cache, ?_, after.ready⟩⟩
      exact fun index publication old => after.retained index publication (reached.retained index publication old)

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain
