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

theorem binds_total (positional named : List Parameter) (varargs : Option Binding) (saved : Bindings)
    (actual : Actual) : ∃ result, Binds positional named varargs saved actual result :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.binds_total
    positional named varargs saved actual

/-- Independent binding agrees with the native binder when there is no keyword collector. -/
theorem binding_exact (signature : Signature) (noKwargs : signature.kwargs = none)
    {saved : Bindings} {actual : Actual} {result : Except Error BoundArguments}
    (source : Binds signature.positional signature.named signature.varargs saved actual result) :
    bindArguments signature saved actual = result :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.binding_exact
    signature noKwargs source

/-- Successful binding can pack the surplus tuple while retaining the reached caller and cells. -/
theorem packs_total (signature : Signature) (noKwargs : signature.kwargs = none)
    (caller : State) (bound : BoundArguments) :
    ∃ assigned packed, Packs signature.varargs caller bound assigned packed ∧
      Body.Keeps caller.heap.size caller packed ∧ packed.bindings = caller.bindings ∧
      packArgs signature bound caller = .ok assigned packed :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.packs_total
    signature noKwargs caller bound

/-- The collector gets the exact ordered surplus at a fresh tuple address. -/
theorem packed_tuple {slot : Binding} {caller packed : State} {bound : BoundArguments} {assigned : Bindings}
    (packing : Packs (some slot) caller bound assigned packed) :
    assigned = (slot, .tuple caller.heap.size) :: bound.named ∧
      Lists.tupleElements caller.heap.size packed = .ok bound.surplusPositional packed :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.packed_tuple
    packing

/-- The empty collector tuple uses the ordinary canonical empty tuple key. -/
theorem packed_empty_key {slot : Binding} {caller packed : State} {bound : BoundArguments} {assigned : Bindings}
    (packing : Packs (some slot) caller bound assigned packed) (empty : bound.surplusPositional = []) :
    packed.heap[caller.heap.size]? = some ⟨.tuple [] (some [.openTuple, .closeTuple]), false⟩ :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.packed_empty_key
    packing empty

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
theorem runs {parent block : LexicalBlock} {formals : List PlainKeywordParameter} {varargs : Option String}
    (site : Site parent formals varargs)
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
