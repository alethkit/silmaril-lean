module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Entry.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.Dispatch

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall

open Block (ModuleBinders)
open Assignment (InOrder)
open Functions
open Lists (State Address Capture Outcome)
open Lists.Iteration (Flow)

local notation "NormalizedExpr" => Functions.Lowering.Resolve.SourceExpr
local notation "ResolvedExpr" => Functions.Lowering.Expr

/-- The source command position identifies the root definition and its
actual declaration table entry after compiling the suffix. -/
theorem checked_root_site (before after : List Command) (chain : Forwarding.Chain) (globals : List String)
    (linked : Program) (resolved : ResolvedModule)
    (binders : ModuleBinders (before ++ .define chain.name (.required chain.parameters) chain.body :: after) globals)
    (checked : resolve (before ++ .define chain.name (.required chain.parameters) chain.body :: after) linked =
      .ok resolved)
    (accepted : ∀ program, Forwarding.Accepted globals program [] chain) (suffixProfile : Segment globals after) :
    ∃ head frames id, Forwarding.Emits globals [] chain (head :: frames) ∧
      resolved.source.commands[before.length]? = some (.exec (.define chain.name id)) ∧
      resolved.program[id]? = some head.declaration :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.checked_root_site
    before after chain globals linked resolved binders checked accepted suffixProfile

/-- The intervening name assignments occupy their corresponding
segment of the compiled command list. -/
theorem checked_writes_site (before after : List Command) {source : List Command}
    {code : List Modules.Command} {globals : List String} {name : String}
    {state final : Lists.State} (writes : Writes globals name state source code final)
    {linked : Program} {resolved : ResolvedModule} (binders : ModuleBinders (before ++ source ++ after) globals)
    (checked : resolve (before ++ source ++ after) linked = .ok resolved) :
    ∃ earlier later, earlier.length = before.length ∧ resolved.source.commands = earlier ++ code ++ later :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.checked_writes_site
    before after writes binders checked

/-- Admitted operands produce ordered values or the reached operand
error in the same state. -/
theorem operands_total {globals : List String} {source : List NormalizedExpr} {resolved : List ResolvedExpr}
    (related : InOrder (Operand globals) source resolved) (state : State) :
    (∃ values, EvaluatesOperands state source (.ok values state)) ∨
      ∃ error, EvaluatesOperands state source (.error error state) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.operands_total
    related state

/-- Successful intervening assignments run with exactly the source
state and preserve the callee binding and closure cell. -/
theorem writes_run_and_keep (program : Program) (host : Catalog)
    {globals : List String} {name : String} {state final : State}
    {source : List Command} {code : List Modules.Command}
    {address : Address} {id : Nat} {captures : List Capture} {frozen : Bool}
    (writes : Writes globals name state source code final)
    (distinct : DistinctOwned state) (live : Live state name address id captures frozen) :
    Modules.Runs program host state code (.ok () final) ∧
      DistinctOwned final ∧ Live final name address id captures frozen :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.writes_run_and_keep
    program host writes distinct live

/-- A normalized evaluation command containing an admitted positional
call emits the corresponding resolved call at its command position. -/
theorem checked_call_site (before after : List Command) (callee : NormalizedExpr) (positional : List NormalizedExpr)
    (function : ResolvedExpr) (actuals : List ResolvedExpr) (globals : List String)
    (linked : Program) (resolved : ResolvedModule)
    (binders : ModuleBinders (before ++ .eval (.call callee positional [] none none) :: after) globals)
    (checked : resolve (before ++ .eval (.call callee positional [] none none) :: after) linked = .ok resolved)
    (related : Operand globals callee function) (arguments : InOrder (Operand globals) positional actuals) :
    resolved.source.commands[before.length]? = some (.exec (.evalExpr (.call function actuals [] none none))) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.checked_call_site
    before after callee positional function actuals globals linked resolved binders checked related arguments

/-- The actual declaration ID from the checked source site supplies
the entry definition step and its live callee. The step starts in the
fresh module frame. -/
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
      DistinctOwned next ∧ Live next chain.name initial.heap.size id captures false :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.checked_root_setup
    before after chain globals linked resolved binders checked accepted suffixProfile caller

/-- The first reached operand error exits the call with its exact
state before expansion, binding, or dispatch. -/
theorem operand_error (program : Program) (available : List DeclarationId) {globals : List String}
    {state next : State} {callee : NormalizedExpr} {positional : List NormalizedExpr}
    {function : ResolvedExpr} {actuals : List ResolvedExpr} {error : Lists.Error}
    (related : Operand globals callee function) (arguments : InOrder (Operand globals) positional actuals)
    (evaluated : EvaluatesOperands state (callee :: positional) (.error error next)) :
    Exec program available state (.evalExpr (.call function actuals [] none none)) (.error error next) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.operand_error
    program available related arguments evaluated

/-- After source operand evaluation succeeds, the independent
positional binder determines arity failure or the exact activation.
The callee-body premise uses the reduced declaration set. -/
theorem checked_invocation {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    {globals : List String} {name : String} {state : State} {positional : List NormalizedExpr} {actuals : List ResolvedExpr}
    {address : Address} {id : Nat} {captures : List Capture} {frozen : Bool} {frame : Forwarding.Frame}
    {values : List Lists.Value} (checked : resolve commands linked = .ok resolved)
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
          | .ok _ => completeCall state none out) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.checked_invocation
    checked callee arguments live found evaluated

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall
