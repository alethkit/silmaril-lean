module

public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Wrapper.Execution
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Wrapper.Prefix

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Wrapper

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Modules (Catalog Executes globalSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (InOrder)
open Silmaril.Languages.Starlark.Modules.Resolve.Block (ModuleBinders)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Forwarding
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Wrapper
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Address Capture Outcome)

local notation "Value" => Silmaril.Languages.Starlark.Lists.Value
local notation "SourceExpr" => Lowering.Resolve.SourceExpr
local notation "Flow" => Silmaril.Languages.Starlark.Lists.Iteration.Flow
local notation "ModuleCommand" => Silmaril.Languages.Starlark.Modules.Command

private theorem preserves_object_write {state : State} {address : Address} {id : Nat} {frame : Frame}
    {captures : List Capture} {frozen : Bool} (closure : ClosureAt state address id frame captures frozen)
    (binding : Binding) (value : Value) :
    ClosureAt (state.write binding value) address id frame captures frozen := by
  refine ⟨?_, closure.environment⟩
  have stored := closure.cell
  unfold State.write
  split <;> try exact stored
  rename_i target owner
  by_cases same : target = address
  · subst target
    simp [stored]
  · split <;> simp [same, stored]

theorem checked_wrapper_assignment {seed : Program} {before after : List Command} {linked : Program}
    {resolved : ResolvedModule} {globals : List String} {outer : List (List String)} {name wrapperName : String} {parameters : List String}
    {child : Chain} {frame childFrame : Frame} {rest : List Frame} {state : State}
    {address : Address} {captures : List Capture} {frozen : Bool}
    {positional : List SourceExpr} {actuals : List Lowering.Expr} {values : List Value}
    (destination : String)
    (binders : ModuleBinders
      (before ++ .assign destination (.call (.scalar (.read name)) positional [] none none) :: after) globals)
    (checked : resolve (before ++ .assign destination (.call (.scalar (.read name)) positional [] none none) :: after)
      linked = .ok resolved)
    (callee : RootCall.Operand globals (.scalar (.read name)) (.atom (.read (.bound (globalSlot name)))))
    (arguments : InOrder (RootCall.Operand globals) positional actuals)
    (evaluated : RootCall.EvaluatesOperands state positional (.ok values state))
    (binding : state.bindingValue (globalSlot name) = .ok (.function address))
    (emits : Emits globals outer (.wrapper wrapperName parameters child) (frame :: childFrame :: rest))
    (links : Links seed (.wrapper wrapperName parameters child) (frame :: childFrame :: rest))
    (keeps : KeepsTable seed resolved.program (frame :: childFrame :: rest))
    (closure : ClosureAt state address (EmittedProgram seed (childFrame :: rest)).size frame captures frozen)
    (host : Catalog) :
    ∃ code out, resolved.source.commands[before.length]? = some code ∧
      Executes resolved.program host state code out ∧
      ((∃ error, Entry.Binds frame.parameters values (.error error) ∧ out = .error (.runtime error) state) ∨
        (∃ assigned selected nextAddress next,
          Entry.Binds frame.parameters values (.ok assigned) ∧
          ReturnsChild seed state child frame childFrame rest captures assigned selected (.ok (.function nextAddress) next) ∧
          out = .ok () (next.write (globalSlot destination) (.function nextAddress)) ∧
          ClosureAt (next.write (globalSlot destination) (.function nextAddress))
            nextAddress (EmittedProgram seed rest).size childFrame selected false)) := by
  let call := Lowering.Expr.call (.atom (.read (.bound (globalSlot name)))) actuals [] none none
  have site := RootCall.checked_call_assignment_site before after destination _ _ _ _ globals linked resolved
    binders checked callee arguments
  let id := (EmittedProgram seed (childFrame :: rest)).size
  have found : resolved.program[id]? = some frame.declaration := keeps _ _ Array.getElem?_push_size
  obtain ⟨result, bound⟩ := Entry.binds_total frame.parameters values
  cases result with
  | error error =>
    have rejected : ExecExpr resolved.program (List.range resolved.program.size) state call (.error error state) :=
      RootCall.checked_invocation_expr checked callee arguments binding closure.cell found evaluated bound
        (.error error state) (by intro assigned impossible; cases impossible)
    exact ⟨_, _, site, .exec (code := .assignExpr destination call) (.assignExpr rejected),
      .inl ⟨error, bound, rfl⟩⟩
  | ok assigned =>
    obtain ⟨selected, returned⟩ := wrapper_total (seed := seed) emits state captures assigned closure.environment
    let address := (activate state frame.declaration captures assigned).heap.size
    obtain ⟨final, ran, restored, escaped⟩ :=
      wrapper_body (withoutDeclaration (List.range resolved.program.size) id) links keeps returned
    have invoked : ExecExpr resolved.program (List.range resolved.program.size) state call
        (.ok (.function address) (restoreCaller state final)) :=
      RootCall.checked_invocation_expr checked callee arguments binding closure.cell found evaluated bound
        (.ok (.returned (.function address)) final) (by intro other same; cases same; exact ran)
    rw [← restored] at invoked
    exact ⟨_, _, site, .exec (code := .assignExpr destination call) (.assignExpr invoked),
      .inr ⟨assigned, selected, address, _, bound, returned, rfl, preserves_object_write escaped _ _⟩⟩

theorem checked_assignment_operand_error {before after : List Command} {linked : Program} {resolved : ResolvedModule}
    {globals : List String} {callee : SourceExpr} {positional : List SourceExpr}
    {function : Lowering.Expr} {actuals : List Lowering.Expr} {state final : State}
    {error : Silmaril.Languages.Starlark.Lists.Error}
    (destination : String)
    (binders : ModuleBinders (before ++ .assign destination (.call callee positional [] none none) :: after) globals)
    (checked : resolve (before ++ .assign destination (.call callee positional [] none none) :: after) linked =
      .ok resolved)
    (related : RootCall.Operand globals callee function)
    (arguments : InOrder (RootCall.Operand globals) positional actuals)
    (evaluated : RootCall.EvaluatesOperands state (callee :: positional) (.error error final))
    (host : Catalog) :
    ∃ code, resolved.source.commands[before.length]? = some code ∧
      Executes resolved.program host state code (.error (.runtime error) final) := by
  have site := RootCall.checked_call_assignment_site before after destination _ _ _ _ globals linked resolved
    binders checked related arguments
  let call := Lowering.Expr.call function actuals [] none none
  have failed := RootCall.operand_error_expr resolved.program (List.range resolved.program.size) related arguments evaluated
  exact ⟨_, site, .exec (code := .assignExpr destination call) (.assignExpr failed)⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Wrapper
