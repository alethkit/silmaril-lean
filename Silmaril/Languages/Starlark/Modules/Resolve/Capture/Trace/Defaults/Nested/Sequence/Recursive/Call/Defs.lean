module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call

open Assignment (LexicalBlock)
open Functions
open Lists (State Outcome)
open Lists.Iteration (Flow finishState)

local notation "NormalizedExpr" => Lowering.Resolve.SourceExpr

local notation "Value" => Lists.Value

/-- Elaborate each positional operand in the caller's lexical block. -/
inductive Arguments (block : LexicalBlock) :
    List NormalizedExpr → List Lowering.Expr → List Binding → Prop where
  | nil : Arguments block [] [] []
  | cons {source : NormalizedExpr} {code : Lowering.Expr} {reads restReads : List Binding}
      {rest : List NormalizedExpr} {codes : List Lowering.Expr} :
      Body.Operand block source code reads → Arguments block rest codes restReads →
      Arguments block (source :: rest) (code :: codes) (reads ++ restReads)

/-- Evaluate the positional operands in order and stop at the first error. -/
inductive Evaluates (block : LexicalBlock) :
    State → List NormalizedExpr → List Lowering.Expr → Outcome (List Value) → Prop where
  | nil {state : State} : Evaluates block state [] [] (.ok [] state)
  | cons {state middle final : State} {source : NormalizedExpr} {code : Lowering.Expr} {value : Value}
      {rest : List NormalizedExpr} {codes : List Lowering.Expr} {values : List Value} :
      Body.Evaluates block state source code (.ok value middle) →
      Evaluates block middle rest codes (.ok values final) →
      Evaluates block state (source :: rest) (code :: codes) (.ok (value :: values) final)
  | headError {state final : State} {source : NormalizedExpr} {code : Lowering.Expr} {error : Lists.Error}
      {rest : List NormalizedExpr} {codes : List Lowering.Expr} :
      Body.Evaluates block state source code (.error error final) →
      Evaluates block state (source :: rest) (code :: codes) (.error error final)
  | tailError {state middle final : State} {source : NormalizedExpr} {code : Lowering.Expr} {value : Value}
      {rest : List NormalizedExpr} {codes : List Lowering.Expr} {error : Lists.Error} :
      Body.Evaluates block state source code (.ok value middle) →
      Evaluates block middle rest codes (.error error final) →
      Evaluates block state (source :: rest) (code :: codes) (.error error final)

@[expose] def expression (name : String) (arguments : List Lowering.Expr) : Lowering.Expr :=
  .call (Leaf.readOperand (fileSlot name)) arguments [] none none

/-- Evidence for the actual record reached at a function value. The
defining frame supplies the addresses and the current heap supplies the
live cells and still-stored default values. -/
structure ClosureAt {parent : LexicalBlock} (site : Site parent)
    (id : DeclarationId) (defining state : State) (address : Nat) where
  captures : List Lists.Capture
  defaults : List Value
  frozen : Bool
  length : defaults.length = site.parameters.optional.length
  recorded : state.heap[address]? = some ⟨.function ⟨id, captures,
    (site.parameters.optional.map (fileSlot ∘ Prod.fst)).zip defaults⟩, frozen⟩
  installed : Installs defining site.free captures
  live : Body.CaptureCells state captures

/-- The body proof operates at the callee's reduced declaration set. -/
abbrev BodyEntry {parent : LexicalBlock} (site : Site parent) (program : Program)
    (available : List DeclarationId) (id : DeclarationId) (bodyRuns : State → Outcome Flow → Prop) : Prop :=
  ∀ (caller defining : State) (captures : List Lists.Capture), Installs defining site.free captures →
    Body.CaptureCells caller captures → ∀ (assigned : List (Binding × Lists.Value)),
    let active := activate caller site.declaration captures assigned
    ∃ out, bodyRuns active out ∧ Exec program (withoutDeclaration available id) active site.body.code out ∧
      Body.Keeps caller.heap.size caller (finishState (Leaf.returnTo caller out))

abbrev BindingRule := List Value → Actual → Except Lists.Error (List (Binding × Value)) → Prop

/-- The call first reads the local callee and then evaluates its
explicit operands. Binding consults the reached heap only after all
operands succeed. A failed bind has no activation premise. -/
inductive RunsPacked {parent : LexicalBlock} (site : Site parent) (bodyRuns : State → Outcome Flow → Prop)
    (block : LexicalBlock)
    (id : DeclarationId) (callee : String) (arguments : List NormalizedExpr) (codes : List Lowering.Expr)
    (collect : List Value → Actual) (binds : BindingRule) : State → Outcome Value → Prop where
  | calleeError {state next : State} {error : Lists.Error} :
      Body.Evaluates block state (.scalar (.read callee)) (Leaf.readOperand (fileSlot callee)) (.error error next) →
      RunsPacked site bodyRuns block id callee arguments codes collect binds state (.error error next)
  | operandError {state next : State} {address : Nat} {error : Lists.Error} :
      Body.Evaluates block state (.scalar (.read callee)) (Leaf.readOperand (fileSlot callee)) (.ok (.function address) state) →
      Evaluates block state arguments codes (.error error next) →
      RunsPacked site bodyRuns block id callee arguments codes collect binds state (.error error next)
  | bindingError {state actualState defining : State} {address : Nat} {values : List Value} {error : Lists.Error} :
      Body.Evaluates block state (.scalar (.read callee)) (Leaf.readOperand (fileSlot callee)) (.ok (.function address) state) →
      Evaluates block state arguments codes (.ok values actualState) →
      (record : ClosureAt site id defining actualState address) →
      binds record.defaults (collect values) (.error error) →
      RunsPacked site bodyRuns block id callee arguments codes collect binds state (.error error actualState)
  | invoked {state actualState defining : State} {address : Nat} {values : List Value} {bodyOut : Outcome Flow}
      {assigned : List (Binding × Value)} :
      Body.Evaluates block state (.scalar (.read callee)) (Leaf.readOperand (fileSlot callee)) (.ok (.function address) state) →
      Evaluates block state arguments codes (.ok values actualState) →
      (record : ClosureAt site id defining actualState address) →
      binds record.defaults (collect values) (.ok assigned) →
      bodyRuns (activate actualState site.declaration record.captures assigned) bodyOut →
      RunsPacked site bodyRuns block id callee arguments codes collect binds state (Leaf.returnTo actualState bodyOut)

abbrev RunsWith {parent : LexicalBlock} (site : Site parent) (bodyRuns : State → Outcome Flow → Prop)
    (block : LexicalBlock) (id : DeclarationId) (callee : String)
    (arguments : List NormalizedExpr) (codes : List Lowering.Expr) :=
  RunsPacked site bodyRuns block id callee arguments codes (fun values => ⟨values, []⟩)
    (fun defaults actual => Binds (site.parameters.slots defaults) actual.positional)

abbrev Runs {parent : LexicalBlock} (site : Site parent) :=
  RunsWith site (fun state out => Sequence.Runs site.block state site.source site.body.code out)

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call
