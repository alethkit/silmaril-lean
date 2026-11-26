module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Defs

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Modules (fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults (missingNames savedValues Parameters)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive (Site)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call (ClosureAt)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Value Error)

private theorem names_total (parameters : List Parameter) (keywords : List (String × Value)) (bound : Bindings) :
    ∃ result, BindsNames parameters bound keywords result := by
  induction keywords generalizing bound with
  | nil => exact ⟨_, .done bound⟩
  | cons keyword rest ih =>
    obtain ⟨name, value⟩ := keyword
    cases found : parameters.find? (fun p => p.slot.name == name) with
    | none => exact ⟨_, .unknown found⟩
    | some formal =>
      cases previous : List.lookup formal.slot bound with
      | some value => exact ⟨_, .conflict found previous⟩
      | none =>
        obtain ⟨result, delivered⟩ := ih ((formal.slot, value) :: bound)
        exact ⟨result, .deliver found previous delivered⟩

theorem binds_total (parameters : List Parameter) (saved : Bindings) (actual : Actual) :
    ∃ result, Binds parameters saved actual result := by
  by_cases surplus : parameters.length < actual.positional.length
  · exact ⟨_, .surplus surplus⟩
  · have enough := Nat.le_of_not_gt surplus
    obtain ⟨result, delivered⟩ := names_total parameters actual.keywords ((parameters.map Parameter.slot).zip actual.positional)
    cases result with
    | error error => exact ⟨_, .rejected enough delivered⟩
    | ok bound =>
      by_cases complete : missingNames (withDefaults parameters bound saved) = []
      · exact ⟨_, .assigned enough delivered complete⟩
      · exact ⟨_, .missing enough delivered complete⟩

private theorem delivered_exact (signature : Signature) (plain : signature.kwargs = none)
    {initial : Bindings} {keywords : List (String × Value)} {result : Except Error Bindings}
    (delivered : BindsNames signature.named initial keywords result) :
    keywords.foldlM (bindKeyword signature) (initial, ([] : List (String × Value))) =
      result.map (fun slots => (slots, [])) := by
  induction delivered with
  | done => rfl
  | unknown find => simp [List.foldlM_cons, bindKeyword, find, plain, bind, Except.bind, Except.map]
  | conflict find previous => simp [List.foldlM_cons, bindKeyword, find, previous, bind, Except.bind, Except.map]
  | deliver find absent _ ih => simpa [List.foldlM_cons, bindKeyword, find, absent, bind, Except.bind] using ih

theorem binding_exact (signature : Signature)
    (ordinary : signature.keywordOnly = []) (noVarargs : signature.varargs = none) (noKwargs : signature.kwargs = none)
    {saved : Bindings} {actual : Actual} {result : Except Error Bindings}
    (source : Binds signature.positional saved actual result) :
    bindArguments signature saved actual = result.map (fun assigned => ⟨assigned, [], []⟩) := by
  have named : signature.named = signature.positional := by simp [Signature.named, ordinary]
  have fold {out : Except Error Bindings}
      (delivered : BindsNames signature.positional ((signature.positional.map Parameter.slot).zip actual.positional)
        actual.keywords out) :
      actual.keywords.foldlM (bindKeyword signature) ((signature.positional.map Parameter.slot).zip actual.positional, []) =
        out.map (fun slots => (slots, [])) := by
    have actualFold := delivered_exact signature noKwargs (named.symm ▸ delivered)
    simpa only [named] using actualFold
  have noSurplus (enough : actual.positional.length ≤ signature.positional.length) :
      actual.positional.drop (signature.positional.map Parameter.slot).length = [] := by
    simp [List.drop_eq_nil_iff, enough]
  cases source with
  | surplus tooMany =>
    have nonempty : (actual.positional.drop signature.positional.length).isEmpty = false := by
      cases reached : actual.positional.drop signature.positional.length with
      | nil => exact (Nat.not_le.mpr tooMany (List.drop_eq_nil_iff.mp reached)).elim
      | cons => rfl
    simp only [bindArguments, List.length_map, noVarargs, nonempty, Bool.not_false,
      Option.isNone_none, Bool.and_self, ite_true]
    rfl
  | rejected enough delivered =>
    simp only [bindArguments, noSurplus enough, List.isEmpty_nil, Bool.not_true, Bool.false_and,
      Bool.false_eq_true, ite_false, fold delivered, Except.map, bind, Except.bind]
  | @missing bound enough delivered incomplete =>
    simp only [bindArguments, noSurplus enough, List.isEmpty_nil, Bool.not_true, Bool.false_and,
      Bool.false_eq_true, ite_false, fold delivered, Except.map, bind, Except.bind, named]
    change (show Except Error BoundArguments from do
      if !(missingNames (withDefaults signature.positional bound saved)).isEmpty then
        throw (.missingArguments (missingNames (withDefaults signature.positional bound saved)))
      return ⟨savedValues (withDefaults signature.positional bound saved), [], []⟩) = _
    cases reached : missingNames (withDefaults signature.positional bound saved) with
    | nil => exact (incomplete reached).elim
    | cons => rfl
  | @assigned bound enough delivered complete =>
    simp only [bindArguments, noSurplus enough, List.isEmpty_nil, Bool.not_true, Bool.false_and,
      Bool.false_eq_true, ite_false, fold delivered, Except.map, bind, Except.bind, named]
    change (show Except Error BoundArguments from do
      if !(missingNames (withDefaults signature.positional bound saved)).isEmpty then
        throw (.missingArguments (missingNames (withDefaults signature.positional bound saved)))
      return ⟨savedValues (withDefaults signature.positional bound saved), [], []⟩) = _
    rw [complete]
    rfl

theorem prepare_exact {parent : LexicalBlock} (site : Site parent) (program : Program) (available : List DeclarationId)
    (id : DeclarationId) (permitted : id ∈ available) (found : program[id]? = some site.declaration)
    {defining state : State} {address : Nat} (record : ClosureAt site id defining state address)
    (actual : Actual) {result : Except Error Bindings} (binding : SiteBinding site record.defaults actual result) :
    prepareExpanded program available actual (.function address) state =
      match result with
      | .error error => .error error state
      | .ok assigned => .ok (.closure ⟨id, permitted, site.declaration.body⟩)
          (activate state site.declaration record.captures assigned) := by
  let saved := (site.parameters.optional.map (fileSlot ∘ Prod.fst)).zip record.defaults
  have loaded : getClosure address state = .ok ⟨id, record.captures, saved⟩ state := by
    simp [getClosure, Silmaril.Languages.Starlark.Lists.projectCell, Silmaril.Languages.Starlark.Lists.getCell,
      bind, EStateM.bind, record.recorded, saved]
    rfl
  have bound : bindArguments site.declaration.signature saved actual =
      result.map (fun assigned => ⟨assigned, [], []⟩) :=
    binding_exact site.declaration.signature rfl rfl rfl binding
  have noVarargs : site.declaration.signature.varargs = none := rfl
  have noKwargs : site.declaration.signature.kwargs = none := rfl
  cases result <;>
    simp only [prepareExpanded, bind, EStateM.bind, loaded, found, permitted, dite_true, bound,
      Except.map, Silmaril.Languages.Starlark.Lists.fromExcept] <;>
    simp [packArgs, noVarargs, noKwargs, pure, EStateM.pure] <;> rfl

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named
