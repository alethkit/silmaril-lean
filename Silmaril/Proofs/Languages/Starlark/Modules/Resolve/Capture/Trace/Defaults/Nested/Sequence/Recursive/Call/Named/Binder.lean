module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Defs

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Modules (fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve (PlainKeywordParameter)
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive (Site)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call (ClosureAt)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Value Error allocateTuple tupleElements projectCell getCell fromExcept)

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

theorem binds_total (positional named : List Parameter) (varargs : Option Binding) (saved : Bindings)
    (actual : Actual) : ∃ result, Binds positional named varargs saved actual result := by
  by_cases surplus : varargs = none ∧ positional.length < actual.positional.length
  · exact ⟨_, .surplus surplus.1 surplus.2⟩
  · have enough : Fits varargs positional actual := fun absent =>
      Nat.le_of_not_gt (fun overflow => surplus ⟨absent, overflow⟩)
    obtain ⟨result, delivered⟩ := names_total named actual.keywords ((positional.map Parameter.slot).zip actual.positional)
    cases result with
    | error error => exact ⟨_, .rejected enough delivered⟩
    | ok bound =>
      by_cases complete : missingNames (withDefaults named bound saved) = []
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

theorem binding_exact (signature : Signature) (noKwargs : signature.kwargs = none)
    {saved : Bindings} {actual : Actual} {result : Except Error BoundArguments}
    (source : Binds signature.positional signature.named signature.varargs saved actual result) :
    bindArguments signature saved actual = result := by
  have fits (enough : Fits signature.varargs signature.positional actual) :
      (!((actual.positional.drop (signature.positional.map Parameter.slot).length).isEmpty) &&
        signature.varargs.isNone) = false := by
    cases h : signature.varargs with
    | none =>
      have drop : actual.positional.drop (signature.positional.map Parameter.slot).length = [] := by
        simp [List.drop_eq_nil_iff, enough h]
      simp only [drop, List.isEmpty_nil, Bool.not_true, Bool.false_and]
    | some slot => simp only [Option.isNone_some, Bool.and_false]
  cases source with
  | surplus noVarargs tooMany =>
    have nonempty : (actual.positional.drop signature.positional.length).isEmpty = false := by
      cases reached : actual.positional.drop signature.positional.length with
      | nil => exact (Nat.not_le.mpr tooMany (List.drop_eq_nil_iff.mp reached)).elim
      | cons => rfl
    simp only [bindArguments, List.length_map, noVarargs, nonempty, Bool.not_false,
      Option.isNone_none, Bool.and_self, ite_true]
    rfl
  | rejected enough delivered =>
    simp only [bindArguments, fits enough, Bool.false_eq_true, ite_false,
      delivered_exact signature noKwargs delivered, Except.map, bind, Except.bind]
  | @missing bound enough delivered incomplete =>
    simp only [bindArguments, fits enough, Bool.false_eq_true, ite_false,
      delivered_exact signature noKwargs delivered, Except.map, bind, Except.bind]
    change (show Except Error BoundArguments from do
      if !(missingNames (withDefaults signature.named bound saved)).isEmpty then
        throw (.missingArguments (missingNames (withDefaults signature.named bound saved)))
      return ⟨savedValues (withDefaults signature.named bound saved),
        actual.positional.drop (signature.positional.map Parameter.slot).length, []⟩) = _
    cases reached : missingNames (withDefaults signature.named bound saved) with
    | nil => exact (incomplete reached).elim
    | cons => rfl
  | @assigned bound enough delivered complete =>
    simp only [bindArguments, fits enough, Bool.false_eq_true, ite_false,
      delivered_exact signature noKwargs delivered, Except.map, bind, Except.bind]
    change (show Except Error BoundArguments from do
      if !(missingNames (withDefaults signature.named bound saved)).isEmpty then
        throw (.missingArguments (missingNames (withDefaults signature.named bound saved)))
      return ⟨savedValues (withDefaults signature.named bound saved),
        actual.positional.drop (signature.positional.map Parameter.slot).length, []⟩) = _
    rw [complete]
    simp only [List.length_map]
    rfl

theorem packs_total (signature : Signature) (noKwargs : signature.kwargs = none)
    (caller : State) (bound : BoundArguments) :
    ∃ assigned packed, Packs signature.varargs caller bound assigned packed ∧
      Body.Keeps caller.heap.size caller packed ∧ packed.bindings = caller.bindings ∧
      packArgs signature bound caller = .ok assigned packed := by
  cases collector : signature.varargs with
  | none =>
    exact ⟨bound.named, caller, .ordinary _ _, ⟨rfl, fun _ _ _ h => h⟩, rfl, by
      simp [packArgs, noKwargs, collector, bind, EStateM.bind, pure, EStateM.pure]⟩
  | some slot =>
    let key := (bound.surplusPositional.mapM fun value => (caller.keyOf value).toOption).map
      (fun parts => .openTuple :: parts.flatten ++ [.closeTuple])
    let packed : State := {caller with heap := caller.heap.push ⟨.tuple bound.surplusPositional key, false⟩}
    have allocated : allocateTuple bound.surplusPositional caller = .ok (.tuple caller.heap.size) packed := rfl
    refine ⟨_, packed, .tuple allocated, ⟨rfl, fun address cell below old => ?_⟩, rfl, ?_⟩
    · simp [packed, Array.getElem?_push, Nat.ne_of_lt below, old]
    · simp [packArgs, noKwargs, collector, bind, EStateM.bind, pure, EStateM.pure, allocated]

theorem packed_tuple {slot : Binding} {caller packed : State} {bound : BoundArguments} {assigned : Bindings}
    (packing : Packs (some slot) caller bound assigned packed) :
    assigned = (slot, .tuple caller.heap.size) :: bound.named ∧
      tupleElements caller.heap.size packed = .ok bound.surplusPositional packed := by
  cases packing with
  | tuple allocated =>
    rcases EStateM.Result.ok.inj allocated with ⟨rfl, rfl⟩
    exact ⟨rfl, by
      simp [tupleElements, projectCell, getCell, bind, EStateM.bind, pure, EStateM.pure]⟩

theorem packed_empty_key {slot : Binding} {caller packed : State} {bound : BoundArguments} {assigned : Bindings}
    (packing : Packs (some slot) caller bound assigned packed) (empty : bound.surplusPositional = []) :
    packed.heap[caller.heap.size]? = some ⟨.tuple [] (some [.openTuple, .closeTuple]), false⟩ := by
  cases packing with
  | tuple allocated =>
    rcases EStateM.Result.ok.inj allocated with ⟨_, rfl⟩
    simp [empty]

theorem prepare_exact {parent : LexicalBlock} {formals : List PlainKeywordParameter} {varargs : Option String}
    (site : Site parent formals varargs) (program : Program) (available : List DeclarationId)
    (id : DeclarationId) (permitted : id ∈ available) (found : program[id]? = some site.declaration)
    {defining state : State} {address : Nat} (record : ClosureAt site id defining state address)
    (actual : Actual) {result : Except Error BoundArguments} (binding : SiteBinding site record.defaults actual result) :
    match result with
    | .error error => prepareExpanded program available actual (.function address) state = .error error state
    | .ok bound => ∃ assigned packed, Packs site.declaration.signature.varargs state bound assigned packed ∧
        Body.Keeps state.heap.size state packed ∧ packed.bindings = state.bindings ∧
        prepareExpanded program available actual (.function address) state =
          .ok (.closure ⟨id, permitted, site.declaration.body⟩)
            (activate packed site.declaration record.captures assigned) := by
  let saved := site.defaultKeys.zip record.defaults
  have loaded : getClosure address state = .ok ⟨id, record.captures, saved⟩ state := by
    simp [getClosure, projectCell, getCell, bind, EStateM.bind, record.recorded, saved]
    rfl
  have boundExact : bindArguments site.declaration.signature saved actual = result :=
    binding_exact site.declaration.signature rfl binding
  cases result with
  | error error =>
    simp only [prepareExpanded, bind, EStateM.bind, loaded, found, permitted, dite_true, boundExact, fromExcept]
    rfl
  | ok bound =>
    obtain ⟨assigned, packed, packing, kept, bindings, exactPack⟩ := packs_total site.declaration.signature rfl state bound
    refine ⟨assigned, packed, packing, kept, bindings, ?_⟩
    simp only [prepareExpanded, bind, EStateM.bind, loaded, found, permitted, dite_true, boundExact, fromExcept,
      pure, EStateM.pure, exactPack]


end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named
