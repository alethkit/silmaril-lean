module

public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Operands
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Binder
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Modules (fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive (Site)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call (BodyEntry ClosureAt)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named hiding Arguments
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Outcome Value)
open Silmaril.Languages.Starlark.Lists.Iteration (Flow finishState)

private theorem expands (state : State) (positional : List Lowering.Expr) (keywords : List (String × Lowering.Expr))
    (values : List Value) :
    Lowering.Expands ((Lowering.argumentShape positional keywords none none).collect values) state
      (.ok (collect positional.length (keywords.map Prod.fst) values) state) := by
  simpa [Lowering.argumentShape, ArgumentShape.collect, collect] using
    Lowering.Expands.success
      (args := ⟨values.take positional.length, (keywords.map Prod.fst).zip (values.drop positional.length), none, none⟩)
      (keys := []) (values := []) (next := state) rfl .empty

theorem runs {parent block : LexicalBlock} (site : Site parent)
    (bodyRuns : State → Outcome Flow → Prop)
    {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (_checked : resolve commands linked = .ok resolved) (id : DeclarationId)
    (found : resolved.program[id]? = some site.declaration)
    (available : List DeclarationId) (permitted : id ∈ available)
    (enterBody : BodyEntry site resolved.program available id bodyRuns)
    {name : String} {state defining : State} {address : Nat}
    (callee : Body.Evaluates block state (.scalar (.read name)) (Leaf.readOperand (fileSlot name))
      (.ok (.function address) state))
    (record : ClosureAt site id defining state address)
    {arguments : List Lowering.Resolve.SourceExpr} {codes : List Lowering.Expr} {reads : List Binding}
    (related : Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Arguments
      block arguments codes reads) (keywords : Operands block) :
    ∃ out, RunsWith site bodyRuns block id name arguments codes keywords.source keywords.codes state out ∧
      ExecExpr resolved.program available state (expression name codes keywords.codes) out ∧
      Lowering.denoteExpr resolved.program available (expression name codes keywords.codes) state = out ∧
      Body.Keeps state.heap.size state (finishState out) :=
  Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.runs_packed
    site bodyRuns resolved.program id available permitted enterBody callee record (ordered_operands related keywords)
    codes keywords.codes rfl _ (SiteBinding site) (fun state values _ => expands state codes keywords.codes values)
    (fun _ _ => binds_total _ _ _) (by
      intro reached closure values result binding
      cases result <;> exact prepare_exact site resolved.program available id permitted found closure _ binding)

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named
