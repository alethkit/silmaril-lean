module

public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.Site
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.Bindings

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall

open Silmaril.Languages.Starlark.Modules (globalSlot enter)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Block (ModuleBinders)
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (InOrder)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall
open Silmaril.Languages.Starlark.Lists (State Address Capture Outcome)
open Silmaril.Languages.Starlark.Lists.Iteration (Flow)
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Functions.Lowering (ClosureRuns)
open Silmaril.Languages.Starlark.Functions.Lowering.Resolve (SourceExpr)

local notation "Value" => Silmaril.Languages.Starlark.Lists.Value
local notation "ModuleCode" => Silmaril.Languages.Starlark.Modules.Command
local notation "ResolvedExpr" => Lowering.Expr

theorem checked_call_site (before after : List Command) (callee : SourceExpr) (positional : List SourceExpr)
    (function : ResolvedExpr) (actuals : List ResolvedExpr) (globals : List String)
    (linked : Program) (resolved : ResolvedModule)
    (binders : ModuleBinders (before ++ .eval (.call callee positional [] none none) :: after) globals)
    (checked : resolve (before ++ .eval (.call callee positional [] none none) :: after) linked = .ok resolved)
    (related : Operand globals callee function) (arguments : InOrder (Operand globals) positional actuals) :
    resolved.source.commands[before.length]? = some (.exec (.evalExpr (.call function actuals [] none none))) := by
  obtain ⟨reads, operand⟩ := resolves_call related arguments
  exact checked_eval_site before after _ _ reads globals linked resolved binders checked operand

theorem checked_call_assignment_site (before after : List Command) (destination : String) (callee : SourceExpr) (positional : List SourceExpr)
    (function : ResolvedExpr) (actuals : List ResolvedExpr) (globals : List String)
    (linked : Program) (resolved : ResolvedModule)
    (binders : ModuleBinders (before ++ .assign destination (.call callee positional [] none none) :: after) globals)
    (checked : resolve (before ++ .assign destination (.call callee positional [] none none) :: after) linked = .ok resolved)
    (related : Operand globals callee function) (arguments : InOrder (Operand globals) positional actuals) :
    resolved.source.commands[before.length]? = some (.exec (.assignExpr destination (.call function actuals [] none none))) := by
  obtain ⟨reads, operand⟩ := resolves_call related arguments
  exact checked_assign_site before after destination _ _ reads globals linked resolved binders checked operand

theorem checked_root_setup (before after : List Command) (chain : Forwarding.Chain) (globals : List String)
    (linked : Program) (resolved : ResolvedModule)
    (binders : ModuleBinders (before ++ .define chain.name (.required chain.parameters) chain.body :: after) globals)
    (checked : resolve (before ++ .define chain.name (.required chain.parameters) chain.body :: after) linked =
      .ok resolved)
    (accepted : ∀ program, Forwarding.Accepted globals program [] chain) (suffixProfile : Segment globals after)
    (caller : State) :
    let initial := enter resolved.source caller
    ∃ head frames id next captures, Forwarding.Emits globals [] chain (head :: frames) ∧
      resolved.source.commands[before.length]? = some (.exec (.define chain.name id)) ∧
      resolved.program[id]? = some head.declaration ∧
      Exec resolved.program (List.range resolved.program.size) initial (.define (globalSlot chain.name) id) (.ok .next next) ∧
      DistinctOwned next ∧ Live next chain.name initial.heap.size id captures false := by
  obtain ⟨head, frames, id, emits, command, found⟩ :=
    checked_root_site before after chain globals linked resolved binders checked accepted suffixProfile
  obtain ⟨next, captures, ran, distinct, live⟩ := root_live binders checked emits
    (List.mem_append_right _ List.mem_cons_self) caller id found
  exact ⟨head, frames, id, next, captures, emits, command, found, ran, distinct, live⟩

theorem operand_error_expr (program : Program) (available : List DeclarationId) {globals : List String}
    {state next : State} {callee : SourceExpr} {positional : List SourceExpr}
    {function : ResolvedExpr} {actuals : List ResolvedExpr} {error : Silmaril.Languages.Starlark.Lists.Error}
    (related : Operand globals callee function) (arguments : InOrder (Operand globals) positional actuals)
    (evaluated : EvaluatesOperands state (callee :: positional) (.error error next)) :
    ExecExpr program available state (.call function actuals [] none none) (.error error next) := by
  have operands := evaluates_operands program available (fun _ _ _ => False) (.cons related arguments) evaluated
  apply ExecExpr.evaluates (calls := fun _ _ _ => False) (fun _ _ _ impossible => impossible.elim)
  exact .callError (by simpa [Lowering.sourceOperands] using operands)

theorem operand_error (program : Program) (available : List DeclarationId) {globals : List String}
    {state next : State} {callee : SourceExpr} {positional : List SourceExpr}
    {function : ResolvedExpr} {actuals : List ResolvedExpr} {error : Silmaril.Languages.Starlark.Lists.Error}
    (related : Operand globals callee function) (arguments : InOrder (Operand globals) positional actuals)
    (evaluated : EvaluatesOperands state (callee :: positional) (.error error next)) :
    Exec program available state (.evalExpr (.call function actuals [] none none)) (.error error next) :=
  .evalExpr (operand_error_expr program available related arguments evaluated)

private theorem evaluation_length {state next : State} {source : List SourceExpr} {values : List Value}
    (evaluated : EvaluatesOperands state source (.ok values next)) : source.length = values.length := by
  generalize eq : (EStateM.Result.ok values next : Outcome (List Value)) = out at evaluated
  induction evaluated generalizing values next with
  | nil => cases eq; rfl
  | @cons first rest value out head tail ih =>
    cases out with
    | error error state => cases eq
    | ok restValues state =>
      cases eq
      simp [ih rfl]
  | error => cases eq

private theorem resolution_length {globals : List String} {source : List SourceExpr} {code : List ResolvedExpr}
    (related : InOrder (Operand globals) source code) : source.length = code.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => simp [ih]

private theorem positioned {code : List ResolvedExpr} {values : List Value} (state : State)
    (length : values.length = code.length) :
    Lowering.Expands ((Lowering.argumentShape code [] none none).collect values) state (.ok ⟨values, []⟩ state) := by
  have shape : (Lowering.argumentShape code [] none none).collect values = ⟨values, [], none, none⟩ := by
    simp [Lowering.argumentShape, ArgumentShape.collect, ← length]
  rw [shape]
  simpa only [List.append_nil] using Lowering.Expands.success (args := ⟨values, [], none, none⟩) (keys := [])
    (values := []) (next := state) rfl .empty

private theorem callee_read {state : State} {name : String} {address : Address}
    (binding : state.bindingValue (globalSlot name) = .ok (.function address)) :
    Evaluates state (.scalar (.read name)) (.ok (.function address) state) := by
  simpa [State.read, binding] using Evaluates.name (state := state) name

/-- Lift a successful source operand spine and an already proved positional
preparation result into the ordinary call rules. -/
theorem prepared_invocation_expr (program : Program) (available : List DeclarationId)
    {globals : List String} {name : String} {state : State} {positional : List SourceExpr} {actuals : List ResolvedExpr}
    {address : Address} {id : Nat} {captures : List Capture} {declaration : Declaration} {values : List Value}
    {result : Except Silmaril.Languages.Starlark.Lists.Error (List (Silmaril.Languages.Starlark.Binding × Value))}
    (permitted : id ∈ available)
    (callee : Operand globals (.scalar (.read name)) (.atom (.read (.bound (globalSlot name)))))
    (arguments : InOrder (Operand globals) positional actuals)
    (binding : state.bindingValue (globalSlot name) = .ok (.function address))
    (evaluated : EvaluatesOperands state positional (.ok values state))
    (prepared : prepareExpanded program available ⟨values, []⟩ (.function address) state =
      match result with
      | .error error => .error error state
      | .ok assigned => .ok (.closure ⟨id, permitted, declaration.body⟩)
        (activate state declaration captures assigned))
    (out : Outcome Flow)
    (bodyRun : ∀ assigned, result = .ok assigned →
      Exec program (withoutDeclaration available id) (activate state declaration captures assigned) declaration.body out) :
    ExecExpr program available state (.call (.atom (.read (.bound (globalSlot name)))) actuals [] none none)
      (match result with
      | .error error => .error error state
      | .ok _ => match out with
        | .ok flow final => .ok (Lowering.callValue flow) (restoreCaller state final)
        | .error error final => .error error (restoreCaller state final)) := by
  have length := (evaluation_length evaluated).symm.trans (resolution_length arguments)
  have expansion := positioned state length
  have ordered : EvaluatesOperands state (.scalar (.read name) :: positional)
      (.ok (.function address :: values) state) := .cons (callee_read binding) evaluated
  let calls : ClosureRuns available := fun plan next outcome =>
    Exec program (withoutDeclaration available plan.id) next plan.body outcome
  have operands := evaluates_operands program available calls (.cons callee arguments) ordered
  have spine : Lowering.sourceOperands (.atom (.read (.bound (globalSlot name)))) actuals [] none none =
      .atom (.read (.bound (globalSlot name))) :: actuals := by simp [Lowering.sourceOperands]
  rw [← spine] at operands
  cases result with
  | error error =>
    exact .evaluates (fun _ _ _ ran => ran) (.call operands (.expanded expansion (.reject prepared)))
  | ok assigned =>
    have runs : calls ⟨id, permitted, declaration.body⟩ (activate state declaration captures assigned) out :=
      bodyRun assigned rfl
    cases out with
    | ok flow final =>
      exact .evaluates (fun _ _ _ ran => ran) (.call operands (.expanded expansion (.returned prepared runs)))
    | error error final =>
      exact .evaluates (fun _ _ _ ran => ran) (.call operands (.expanded expansion (.failed prepared runs)))

theorem checked_invocation_expr {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    {globals : List String} {name : String} {state : State} {positional : List SourceExpr} {actuals : List ResolvedExpr}
    {address : Address} {id : Nat} {captures : List Capture} {frozen : Bool} {frame : Forwarding.Frame}
    {values : List Value} (checked : resolve commands linked = .ok resolved)
    (callee : Operand globals (.scalar (.read name)) (.atom (.read (.bound (globalSlot name)))))
    (arguments : InOrder (Operand globals) positional actuals)
    (binding : state.bindingValue (globalSlot name) = .ok (.function address))
    (cell : state.heap[address]? = some ⟨.function ⟨id, captures, []⟩, frozen⟩)
    (found : resolved.program[id]? = some frame.declaration)
    (evaluated : EvaluatesOperands state positional (.ok values state))
    {result : Except Silmaril.Languages.Starlark.Lists.Error (List (Silmaril.Languages.Starlark.Binding × Value))}
    (binds : Entry.Binds frame.parameters values result) (out : Outcome Flow)
    (bodyRun : ∀ assigned, result = .ok assigned →
      Exec resolved.program (withoutDeclaration (List.range resolved.program.size) id)
        (activate state frame.declaration captures assigned) frame.code out) :
    ExecExpr resolved.program (List.range resolved.program.size) state
      (.call (.atom (.read (.bound (globalSlot name)))) actuals [] none none)
      (match result with
      | .error error => .error error state
      | .ok _ => match out with
        | .ok flow final => .ok (Lowering.callValue flow) (restoreCaller state final)
        | .error error final => .error error (restoreCaller state final)) := by
  let available := List.range resolved.program.size
  have permitted : id ∈ available := List.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).choose
  have prepare := Entry.checked_prepare checked available frame id permitted state address captures frozen values result
    cell found binds
  cases result with
  | error error =>
    exact prepared_invocation_expr resolved.program available (declaration := frame.declaration)
      (captures := captures) (result := .error error) permitted callee arguments binding evaluated prepare out bodyRun
  | ok assigned =>
    cases out <;> exact prepared_invocation_expr resolved.program available (declaration := frame.declaration)
      (captures := captures) (result := .ok assigned) permitted callee arguments binding evaluated prepare _ bodyRun

theorem checked_invocation {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    {globals : List String} {name : String} {state : State} {positional : List SourceExpr} {actuals : List ResolvedExpr}
    {address : Address} {id : Nat} {captures : List Capture} {frozen : Bool} {frame : Forwarding.Frame}
    {values : List Value} (checked : resolve commands linked = .ok resolved)
    (callee : Operand globals (.scalar (.read name)) (.atom (.read (.bound (globalSlot name)))))
    (arguments : InOrder (Operand globals) positional actuals)
    (live : Live state name address id captures frozen) (found : resolved.program[id]? = some frame.declaration)
    (evaluated : EvaluatesOperands state positional (.ok values state)) :
    ∃ result, Entry.Binds frame.parameters values result ∧
      ∀ (out : Outcome Flow),
        (∀ assigned, result = .ok assigned →
          Exec resolved.program (withoutDeclaration (List.range resolved.program.size) id)
            (activate state frame.declaration captures assigned) frame.code out) →
        Exec resolved.program (List.range resolved.program.size) state
          (.evalExpr (.call (.atom (.read (.bound (globalSlot name)))) actuals [] none none))
          (match result with
          | .error error => .error error state
          | .ok _ => completeCall state none out) := by
  obtain ⟨result, binds⟩ := Entry.binds_total frame.parameters values
  refine ⟨result, binds, ?_⟩
  intro out bodyRun
  have invoked := checked_invocation_expr checked callee arguments live.binding live.cell found evaluated binds out bodyRun
  cases result with
  | error error => exact .evalExpr invoked
  | ok assigned => cases out <;> exact .evalExpr invoked

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall
