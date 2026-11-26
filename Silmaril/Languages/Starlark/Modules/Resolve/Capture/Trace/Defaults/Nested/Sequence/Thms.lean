module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Run

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence

open Assignment (LexicalBlock)
open Functions
open Lists (State)
open Lists.Iteration (finishState)

/-- The declarative sequence agrees with the existing normalized compiler. -/
theorem compiles {block : LexicalBlock} {source : Statement} {seed final : Program} {resolved : ResolvedBody}
    (profile : Elaborates block source seed resolved final) :
    compileBody ⟨block.context, .local⟩ source seed = .ok (resolved, final) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.compiles profile

theorem collects {block : LexicalBlock} {source : Statement} {seed final : Program} {resolved : ResolvedBody}
    (profile : Elaborates block source seed resolved final) :
    ∃ occurrences, Block.BodyBinders source occurrences :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.collects profile

theorem preserves_declarations {block : LexicalBlock} {source : Statement}
    {seed final : Program} {resolved : ResolvedBody}
    (profile : Elaborates block source seed resolved final) :
    PreservesDeclarations seed final :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.preserves_declarations profile

theorem selects {block : LexicalBlock} {source : Statement} {seed final : Program} {resolved : ResolvedBody}
    (profile : Elaborates block source seed resolved final) :
    ∃ free, Selects block resolved.reads free :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.selects profile

/-- Execute a checked suite from its active frame. A reached definition
derives its declaration lookup and ordered captures, then hands its
installed state to the remaining source. Each error stops immediately. -/
theorem runs {block : LexicalBlock} {source : Statement} {seed final : Program} {resolved : ResolvedBody}
    (profile : Elaborates block source seed resolved final) (program : Program)
    (linked : PreservesDeclarations final program) (available : List DeclarationId)
    {before after : List Binding} {free : List FreeName}
    (selection : Selects block (before ++ resolved.reads ++ after) free) (state : State) {floor : Nat}
    (frame : Body.Frame block free floor state) :
    ∃ out, Runs block state source resolved.code out ∧ Body.Frame block free floor (finishState out) ∧
      Body.Keeps floor state (finishState out) ∧ Exec program available state resolved.code out ∧
      denoteBody program available resolved.code state = out :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.runs profile
    program linked available selection state frame

/-- A reached successful definition identifies the actual closure and
saved defaults before any subsequent rebind. -/
theorem installation {block : LexicalBlock} {child : Body.Definition} (plan : Nested.Plan block child)
    {id : DeclarationId} {captures : List Lists.Capture} {start installed : State}
    (result : Nested.DefinitionResult plan id captures start (.ok .next installed)) :
    Nonempty (Installed plan id captures installed) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.installation plan result

/-- A subsequent operand that reaches the same function record can use
the independent binder to prepare a checked positional invocation. -/
theorem prepare_installed {block : LexicalBlock} {child : Body.Definition}
    {plan : Nested.Plan block child} {id : DeclarationId} {captures : List Lists.Capture}
    {installed : State} (origin : Installed plan id captures installed)
    {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (found : resolved.program[id]? = some plan.declaration)
    (later : State) (frozen : Bool) (actuals : List Lists.Value)
    (recorded : later.heap[origin.address]? = some ⟨.function ⟨id, captures,
      (child.parameters.optional.map (fileSlot ∘ Prod.fst)).zip origin.values⟩, frozen⟩) :
    let available := List.range resolved.program.size
    ∃ result, Defaults.Binds (child.parameters.slots origin.values) actuals result ∧
      ∃ permitted : id ∈ available,
        prepareExpanded resolved.program available ⟨actuals, []⟩ (.function origin.address) later =
          match result with
          | .error error => .error error later
          | .ok assigned => .ok (.closure ⟨id, permitted, plan.declaration.body⟩)
            (activate later plan.declaration captures assigned) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.prepare_installed
    origin checked found later frozen actuals recorded

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence
