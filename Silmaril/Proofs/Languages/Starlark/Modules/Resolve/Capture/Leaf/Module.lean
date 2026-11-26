module

public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Leaf.Eval
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Leaf.Link
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Leaf.Publication

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Leaf

open Silmaril.Languages.Starlark.Modules (Catalog Executes Published enter globalSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Block (ModuleBinders)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Leaf
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Address Capture Outcome)
open Silmaril.Languages.Starlark.Lists.Iteration (Flow)

local notation "Binding" => Silmaril.Languages.Starlark.Binding
local notation "Value" => Silmaril.Languages.Starlark.Lists.Value
local notation "ModuleResult" => Silmaril.Languages.Starlark.Modules.Result

theorem body_sound (program : Program) (available : List DeclarationId) (caller : State)
    (frame : Forwarding.Frame) (captures : List Capture) (assigned : List (Binding × Value))
    {out : Outcome Value} (source : BodyRuns program caller frame captures assigned out) :
    ∃ bodyOut, Exec program available (activate caller frame.declaration captures assigned) frame.code bodyOut ∧
      returnTo caller bodyOut = out := by
  cases source with
  | wrapper links keeps returned =>
    obtain ⟨final, ran, restore, _⟩ := Wrapper.wrapper_body available links keeps returned
    exact ⟨_, ran, by simp [returnTo, Lowering.callValue, restore]⟩
  | leaf compiled lexical legal owned free ran =>
    have clean := activate_no_private caller frame captures assigned owned free
    have result := leaf_denotes program available _ _ legal clean ran
    rw [← code_of_lexical compiled lexical] at result
    exact ⟨_, (exec_iff_denoteBody _ _ _ _ _).mpr result, rfl⟩

private theorem setup_eval (program : Program) (available : List DeclarationId) {globals : List String}
    {state : State} {source : Lowering.Resolve.SourceExpr} {code : Lowering.Expr} {out : Outcome Value}
    (setup : Setup globals state source code out) : ExecExpr program available state code out := by
  apply ExecExpr.evaluates (calls := fun _ _ _ => False) (fun _ _ _ impossible => impossible.elim)
  cases setup with
  | atom related evaluated =>
    exact RootCall.evaluates_operand program available _ related evaluated
  | list related evaluated =>
    exact .list (RootCall.evaluates_operands program available _ related evaluated)
  | tuple related evaluated =>
    exact .tuple (RootCall.evaluates_operands program available _ related evaluated)

private theorem assigned (program : Program) (host : Catalog) (state : State) (destination : String)
    (expr : Lowering.Expr) (out : Outcome Value)
    (evaluated : ExecExpr program (List.range program.size) state expr out) :
    Executes program host state (.exec (.assignExpr destination expr)) (assignResult destination out) := by
  cases out <;> exact .exec (code := .assignExpr destination expr) (.assignExpr evaluated)

theorem step_sound {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    {globals : List String} (checked : resolve commands linked = .ok resolved) (host : Catalog)
    {index : Nat} {state : State} {command : Command} {out : ModuleResult Unit}
    (stepped : Step resolved globals index state command out) :
    ∃ code, resolved.source.commands[index]? = some code ∧ Executes resolved.program host state code out := by
  let available := List.range resolved.program.size
  cases stepped with
  | @define index name parameters body id frame captures site found installed =>
    have addresses : frame.declaration.free.mapM (captureName state) = .ok captures :=
      installs_lookup state installed
    have noDefaults : frame.declaration.signature.defaulted = [] := by
      simp [Forwarding.Frame.declaration, requiredSignature, Signature.defaulted, Signature.named, List.filterMap_map]
    have noOperands : defaultOperands resolved.program id = [] := by
      simp [defaultOperands, found, noDefaults]
    have defaults : ExecExprs resolved.program available state (defaultOperands resolved.program id) (.ok [] state) := by
      rw [noOperands]
      exact .evaluatesMany (calls := fun _ _ _ => False) (fun _ _ _ impossible => impossible.elim) .empty
    refine ⟨_, site, ?_⟩
    have ran := Executes.exec (host := host) (code := .define name id)
      (Exec.define (target := globalSlot name) defaults)
    simpa [Silmaril.Languages.Starlark.Modules.afterCode, define, Outcome.resume, found, addresses,
      noDefaults] using ran
  | @setup index name source code out site setup =>
    exact ⟨_, site, assigned resolved.program host state name code out (setup_eval _ _ setup)⟩
  | operandError site callee arguments evaluated =>
    exact ⟨_, site, .exec (code := .assignExpr _ _)
      (.assignExpr (RootCall.operand_error_expr _ _ callee arguments evaluated))⟩
  | @call declId commandIndex name destination positional actuals values frame address captures frozen
      result out site callee arguments evaluated binding stored found bound invoked =>
    cases result with
    | error error =>
      change out = .error error state at invoked
      subst out
      have ran := RootCall.checked_invocation_expr checked callee arguments binding stored found evaluated bound
        (.error error state) (by intro assigned impossible; cases impossible)
      exact ⟨_, site, assigned resolved.program host state destination _ _ ran⟩
    | ok parameters =>
      obtain ⟨bodyOut, ran, same⟩ := body_sound resolved.program (withoutDeclaration available declId)
        state frame captures parameters invoked
      have expression := RootCall.checked_invocation_expr checked callee arguments binding stored found evaluated bound
        bodyOut (by intro assigned eq; cases eq; exact ran)
      subst out
      cases bodyOut <;> exact ⟨_, site, assigned resolved.program host state destination _ _ expression⟩

theorem checked_first_definition (after : List Command) (chain : Forwarding.Chain)
    (globals : List String) (linked : Program) (resolved : ResolvedModule)
    (declared : ModuleBinders (.define chain.name (.required chain.parameters) chain.body :: after) globals)
    (checked : resolve (.define chain.name (.required chain.parameters) chain.body :: after) linked = .ok resolved)
    (accepted : ∀ program, Forwarding.Accepted globals program [] chain)
    (suffix : RootCall.Segment globals after) (caller : State) :
    ∃ seed frame rest next,
      Forwarding.Emits globals [] chain (frame :: rest) ∧
      Forwarding.Links seed chain (frame :: rest) ∧
      Wrapper.KeepsTable seed resolved.program (frame :: rest) ∧
      Step resolved globals 0 (enter resolved.source caller)
        (.define chain.name (.required chain.parameters) chain.body) (.ok () next) := by
  obtain ⟨seed, frame, rest, emitted, links, site, kept⟩ :=
    RootCall.checked_chain_site [] after chain globals linked resolved declared checked accepted suffix
  have found : resolved.program[(Forwarding.EmittedProgram seed rest).size]? = some frame.declaration :=
    kept _ _ (by simp [Forwarding.EmittedProgram])
  obtain ⟨_, captures, installed, _⟩ :=
    Entry.checked_root_definition declared checked emitted (by simp) caller _ found
  exact ⟨seed, frame, rest, _, emitted, links, kept, .define site found installed⟩

theorem checked_module {commands : List Command} {globals : List String} {linked : Program}
    {resolved : ResolvedModule} {out : ModuleResult Unit} {published : ModuleResult Published}
    (declared : ModuleBinders commands globals) (checked : resolve commands linked = .ok resolved)
    (host : Catalog) (caller : State)
    (reached : Wrapper.ReachedPrefix (Step resolved globals) 0 (enter resolved.source caller) commands out)
    (observes : Finishes globals caller out published) :
    Initializes commands host caller linked (.ok published) ∧ runModule commands host caller linked = .ok published :=
  module_observes declared checked host caller (fun _ _ _ _ => step_sound checked host) reached observes

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Leaf
