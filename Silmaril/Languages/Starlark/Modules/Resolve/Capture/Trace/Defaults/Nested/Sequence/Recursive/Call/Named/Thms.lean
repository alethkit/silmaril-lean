module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Execution

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named

open Assignment (LexicalBlock)
open Functions
open Functions.Lowering.Resolve (resolveTracked)
open Lists (State Outcome)
open Lists.Iteration (Flow finishState)

local notation "Value" => Lists.Value
local notation "Error" => Lists.Error
local notation "Positional" =>
  Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Arguments
local notation "NamedArgs" => Arguments

theorem binds_total (parameters : List Parameter) (saved : Bindings) (actual : Actual) :
    ∃ result, Binds parameters saved actual result :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.binds_total
    parameters saved actual

/-- Independent keyword delivery agrees with the shared binder on the plain signature. -/
theorem binding_exact (signature : Signature)
    (ordinary : signature.keywordOnly = []) (noVarargs : signature.varargs = none) (noKwargs : signature.kwargs = none)
    {saved : Bindings} {actual : Actual} {result : Except Error Bindings}
    (source : Binds signature.positional saved actual result) :
    bindArguments signature saved actual = result.map (fun assigned => ⟨assigned, [], []⟩) :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.binding_exact
    signature ordinary noVarargs noKwargs source

theorem argument_origins {block : LexicalBlock}
    {source : List (String × Lowering.Resolve.SourceExpr)} {codes : List (String × Lowering.Expr)} {reads : List Binding}
    (related : NamedArgs block source codes reads) :
    ∀ binding ∈ reads, ∃ origin, Silmaril.Languages.Starlark.Modules.Resolve.Capture.ReadOrigin block binding origin :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.argument_origins
    related

/-- Normalized resolution keeps the callee, positional reads and named reads in their source order. -/
theorem resolves {block : LexicalBlock} {name : String}
    {positional : List Lowering.Resolve.SourceExpr} {posCodes : List Lowering.Expr} {posReads : List Binding}
    (legal : name.toList.head? ≠ some '$') (owned : name ∈ block.owned)
    (related : Positional block positional posCodes posReads) (keywords : Operands block) :
    resolveTracked block.context (.call (.scalar (.read name)) positional keywords.source none none) =
      .ok (expression name posCodes keywords.codes, fileSlot name :: (posReads ++ keywords.reads)) :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.resolves
    legal owned related keywords

/-- The accepted operand profile emits distinct explicit keyword names. -/
theorem distinct_names {block : LexicalBlock} (keywords : Operands block) :
    firstDuplicate (keywords.codes.map Prod.fst) = none :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.distinct_names
    keywords

/-- Repeated explicit names are rejected during validation, before the call can run. -/
theorem rejects_duplicate (name : String) (positional : List Lowering.Expr)
    (keywords : List (String × Lowering.Expr)) (duplicate : String)
    (repeated : firstDuplicate (keywords.map Prod.fst) = some duplicate) :
    (expression name positional keywords).validateCalls = .error (.duplicateExplicitKeyword duplicate) :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.rejects_duplicate
    name positional keywords duplicate repeated

/-- The reached closure uses its saved defaults and live captures under the same declaration guard. -/
theorem runs {parent block : LexicalBlock} (site : Site parent)
    (bodyRuns : State → Outcome Flow → Prop)
    {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (id : DeclarationId)
    (found : resolved.program[id]? = some site.declaration)
    (available : List DeclarationId) (permitted : id ∈ available)
    (enterBody : BodyEntry site resolved.program available id bodyRuns)
    {name : String} {state defining : State} {address : Nat}
    (callee : Body.Evaluates block state (.scalar (.read name)) (Leaf.readOperand (fileSlot name))
      (.ok (.function address) state))
    (record : ClosureAt site id defining state address)
    {arguments : List Lowering.Resolve.SourceExpr} {codes : List Lowering.Expr} {reads : List Binding}
    (related : Positional block arguments codes reads) (keywords : Operands block) :
    ∃ out, RunsWith site bodyRuns block id name arguments codes keywords.source keywords.codes state out ∧
      ExecExpr resolved.program available state (expression name codes keywords.codes) out ∧
      Lowering.denoteExpr resolved.program available (expression name codes keywords.codes) state = out ∧
      Body.Keeps state.heap.size state (finishState out) :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.runs
    site bodyRuns checked id found available permitted enterBody callee record related keywords

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named
