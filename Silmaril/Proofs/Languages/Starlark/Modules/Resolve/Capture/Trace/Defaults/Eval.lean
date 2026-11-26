module

public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Binder
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Steps
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.Heap

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Modules (fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Functions
open Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings (Preserves)
open Silmaril.Languages.Starlark.Lists (State Outcome Address Capture)
open Silmaril.Languages.Starlark.Lists.Iteration (Flow)
open Silmaril.Languages.Starlark.Functions.Lowering.Resolve (SourceExpr resolveTracked)

local notation "Value" => Silmaril.Languages.Starlark.Lists.Value

theorem setup_eval (program : Program) (available : List DeclarationId) {globals : List String}
    {state : State} {source : SourceExpr} {code : Lowering.Expr} {out : Outcome Value}
    (setup : Leaf.Setup globals state source code out) :
    Lowering.EvaluatesWith program available (fun _ _ _ => False) (fun _ => True) state code out := by
  cases setup with
  | atom related evaluated => exact RootCall.evaluates_operand program available _ related evaluated
  | list related evaluated => exact .list (RootCall.evaluates_operands program available _ related evaluated)
  | tuple related evaluated => exact .tuple (RootCall.evaluates_operands program available _ related evaluated)

private theorem default_eval (program : Program) (available : List DeclarationId) {globals : List String}
    {state : State} {sources : List SourceExpr} {codes : List Lowering.Expr} {out : Outcome (List Value)}
    (evaluated : Evaluates globals state sources codes out) :
    Lowering.EvaluatesManyWith program available (fun _ _ _ => False) (fun _ => True) state codes out := by
  induction evaluated with
  | nil => exact .empty
  | error first => exact .headError (setup_eval program available first)
  | @next state middle first code value rest codes out firstRan restRan ih =>
    cases out with
    | error => exact .tailError (setup_eval program available firstRan) ih
    | ok => exact .cons (setup_eval program available firstRan) ih

private theorem evaluation_count {globals : List String} {state : State}
    {sources : List SourceExpr} {codes : List Lowering.Expr} {out : Outcome (List Value)}
    (ran : Evaluates globals state sources codes out) :
    ∀ values next, out = .ok values next → values.length = sources.length := by
  induction ran with
  | nil => intro _ _ same; cases same; rfl
  | error => intro _ _ same; cases same
  | @next _ _ _ _ _ _ _ out _ _ ih =>
    intro values next same
    cases out with
    | error => cases same
    | ok =>
      cases same
      simp [ih _ _ rfl]

theorem evaluated_length {globals : List String} {state final : State}
    {sources : List SourceExpr} {codes : List Lowering.Expr} {values : List Value}
    (evaluated : Evaluates globals state sources codes (.ok values final)) : values.length = sources.length :=
  evaluation_count evaluated _ _ rfl

private theorem defaults_step {globals : List String} {defined : List PlainPositionalDefault}
    (accepted : ∀ item ∈ defined, Initializer globals item.source)
    (translated : ∀ item ∈ defined, resolveTracked ⟨[], globals⟩ item.source = .ok (item.value, item.reads))
    (state : State) :
    ∃ out, Evaluates globals state (defined.map PlainPositionalDefault.source)
      (defined.map PlainPositionalDefault.value) out ∧
      (∀ value next, out = .ok value next → Preserves state next) := by
  induction defined generalizing state with
  | nil => exact ⟨_, .nil, fun _ _ equal => by cases equal; exact Preserves.refl _⟩
  | cons head rest ih =>
    obtain ⟨code, reads, out, tracked, evaluated, extension⟩ := setup_value (accepted head (by simp)) state
    have equal := (translated head (by simp)).symm.trans tracked
    obtain ⟨codeEq, readsEq⟩ := Prod.mk.inj (Except.ok.inj equal)
    subst code
    subst reads
    cases out with
    | error => exact ⟨_, .error evaluated, fun _ _ impossible => nomatch impossible⟩
    | ok value middle =>
      obtain ⟨out, restRan, kept⟩ := ih
        (fun item member => accepted item (List.mem_cons_of_mem _ member))
        (fun item member => translated item (List.mem_cons_of_mem _ member)) middle
      refine ⟨_, .next evaluated restRan, ?_⟩
      intro _ next equal
      have first : Preserves state middle := by
        rcases extension value middle rfl with rfl | ⟨cell, rfl⟩
        · exact Preserves.refl _
        · exact Preserves.push _ cell
      cases out with
      | error => cases equal
      | ok values final =>
        cases equal
        exact first.trans (kept values _ rfl)

theorem evaluates_from_source {globals : List String} {source : List (String × SourceExpr)}
    (admitted : ∀ item ∈ source, Initializer globals item.2) :
    ∃ defined : List PlainPositionalDefault,
      defined.map (fun item => (item.name, item.source)) = source ∧
      (∀ item ∈ defined, resolveTracked ⟨[], globals⟩ item.source = .ok (item.value, item.reads)) ∧
      ∀ state, ∃ out, Evaluates globals state (source.map Prod.snd)
        (defined.map PlainPositionalDefault.value) out ∧
        (∀ value next, out = .ok value next → Preserves state next) := by
  have static : ∃ defined : List PlainPositionalDefault,
      defined.map (fun item => (item.name, item.source)) = source ∧
      (∀ item ∈ defined, resolveTracked ⟨[], globals⟩ item.source = .ok (item.value, item.reads)) := by
    induction source with
    | nil => exact ⟨[], rfl, by simp⟩
    | cons head rest ih =>
      obtain ⟨code, reads, _, checked, _, _⟩ := setup_value (admitted head (by simp)) {}
      obtain ⟨tail, identified, compiled⟩ := ih (fun item member => admitted item (List.mem_cons_of_mem _ member))
      refine ⟨⟨head.1, head.2, code, reads⟩ :: tail, ?_, ?_⟩
      · simp [identified]
      · intro item member
        rcases List.mem_cons.mp member with rfl | later
        · exact checked
        · exact compiled item later
  obtain ⟨defined, same, translated⟩ := static
  refine ⟨defined, same, translated, fun state => ?_⟩
  have accepted (item : PlainPositionalDefault) (member : item ∈ defined) : Initializer globals item.source :=
    admitted (item.name, item.source) (same ▸ List.mem_map_of_mem member)
  have sources : defined.map PlainPositionalDefault.source = source.map Prod.snd := by
    rw [← same]
    simp [List.map_map, Function.comp_def]
  rw [← sources]
  exact defaults_step accepted translated state

theorem definition_sound (program : Program) (available : List DeclarationId) (target : Binding)
    (id : Nat) (parameters : Parameters) (codes : List Lowering.Expr) (declaration : Declaration)
    (found : program[id]? = some declaration)
    (defaults : declaration.signature.defaulted =
      (parameters.optional.map (fileSlot ∘ Prod.fst)).zip codes)
    (length : codes.length = parameters.optional.length)
    {globals : List String} {state : State} {out : Outcome Flow}
    (source : Defines globals target id declaration.free parameters codes state out) :
    Exec program available state (.define target id) out ∧
      denoteBody program available (.define target id) state = out := by
  have ordered : defaultOperands program id = codes := by
    simp [defaultOperands, found, defaults, List.map_snd_zip, length]
  have operands {out : Outcome (List Value)}
      (evaluated : Evaluates globals state (parameters.optional.map Prod.snd) codes out) :
      ExecExprs program available state (defaultOperands program id) out := by
    rw [ordered]
    exact .evaluatesMany (calls := fun _ _ _ => False) (fun _ _ _ impossible => impossible.elim)
      (default_eval program available evaluated)
  have ran : Exec program available state (.define target id) out := by
    cases source with
    | failed evaluated => exact .define (operands evaluated)
    | installed evaluated capturesInstalled =>
      have keys : declaration.signature.defaulted.map Prod.fst =
          parameters.optional.map (fileSlot ∘ Prod.fst) := by
        rw [defaults]
        simp [List.map_fst_zip, length]
      have actual := Exec.define (target := target) (operands evaluated)
      simpa [Outcome.resume, define, found, installs_lookup _ capturesInstalled, keys, install] using actual
  exact ⟨ran, (exec_iff_denoteBody _ _ _ _ _).mp ran⟩

theorem prepare_saved (program : Program) (available : List DeclarationId) (declaration : Declaration)
    (id : Nat) (permitted : id ∈ available) (state : State) (address : Address)
    (captures : List Capture) (frozen : Bool) (slots : List (Binding × Option Value)) (values : List Value)
    (cell : state.heap[address]? = some ⟨.function ⟨id, captures, savedValues slots⟩, frozen⟩)
    (found : program[id]? = some declaration)
    (positional : declaration.signature.positional.map Parameter.slot = slots.map Prod.fst)
    (unique : (slots.map Prod.fst).Nodup)
    (keywords : declaration.signature.keywordOnly = []) (varargs : declaration.signature.varargs = none)
    (kwargs : declaration.signature.kwargs = none)
    {result : Except Silmaril.Languages.Starlark.Lists.Error (List (Binding × Value))}
    (binding : Binds slots values result) :
    prepareExpanded program available ⟨values, []⟩ (.function address) state =
      match result with
      | .error error => .error error state
      | .ok assigned =>
        .ok (.closure ⟨id, permitted, declaration.body⟩) (activate state declaration captures assigned) := by
  have bound := binding_exact declaration.signature slots positional unique keywords varargs values binding
  have loaded : getClosure address state = .ok ⟨id, captures, savedValues slots⟩ state := by
    simp [getClosure, Silmaril.Languages.Starlark.Lists.projectCell, Silmaril.Languages.Starlark.Lists.getCell,
      bind, EStateM.bind, cell]
    rfl
  cases result <;>
    simp only [prepareExpanded, bind, EStateM.bind, loaded, found, permitted, dite_true, bound,
      Except.map, Silmaril.Languages.Starlark.Lists.fromExcept] <;>
    simp [packArgs, varargs, kwargs, pure, EStateM.pure] <;> rfl

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
