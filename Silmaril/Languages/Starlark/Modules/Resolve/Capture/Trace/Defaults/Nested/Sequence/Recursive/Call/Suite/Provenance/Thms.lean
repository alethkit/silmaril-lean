module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall.Thms
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance.Execution

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance

open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open RootCall (DistinctOwned)
open Functions
open Lists (State Capture)
open Lists.Iteration (finishState)

/-- The independent suite and lexical read order agree with normalized compilation. -/
theorem compiles {block : LexicalBlock} {locals : Locals block} {source : Statement} {seed final : Program}
    {code : ResolvedBody} {emissions : Emissions} (profile : Elaborates block locals source seed code final emissions) :
    compileBody ⟨block.context, .local⟩ source seed = .ok (code, final) :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance.compiles profile

theorem collects {block : LexicalBlock} {locals : Locals block} {source : Statement} {seed final : Program}
    {code : ResolvedBody} {emissions : Emissions} (profile : Elaborates block locals source seed code final emissions) :
    ∃ names, Block.BodyBinders source names :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance.collects profile

/-- Each emitted declaration keeps its actual table index. -/
theorem links {block : LexicalBlock} {locals : Locals block} {source : Statement} {seed final : Program}
    {code : ResolvedBody} {emissions : Emissions} (profile : Elaborates block locals source seed code final emissions) :
    PreservesDeclarations seed final ∧ ∀ entry ∈ emissions, final[entry.1]? = some entry.2 :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance.links profile

theorem selects {block : LexicalBlock} {locals : Locals block} {source : Statement} {seed final : Program}
    {code : ResolvedBody} {emissions : Emissions} (profile : Elaborates block locals source seed code final emissions) :
    ∃ free, Selects block code.reads free :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance.selects profile

/-- A suite entered under the full table with its own ID removed has all its child IDs. -/
theorem entry_guard {block : LexicalBlock} {locals : Locals block} {source : Statement} {seed final program : Program}
    {code : ResolvedBody} {emissions : Emissions} (profile : Elaborates block locals source seed code final emissions)
    (table : PreservesDeclarations final program) :
    List.Subset (emissions.map Prod.fst) (withoutDeclaration (List.range program.size) final.size) :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance.entry_guard profile table

/-- Read-only operands and restored child calls keep the tracked caller bindings and records. -/
theorem keeps_live {block : LexicalBlock} {locals : Locals block} {state next : State}
    (live : Live locals state) (kept : Body.Keeps state.heap.size state next) : Live locals next :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance.keeps_live live kept

/-- Read the actual local binding, retaining the closure record at its reached address. -/
theorem evaluated_local {block : LexicalBlock} {locals : Locals block} {state : State}
    {name : String} {entry : Entry block} (live : Live locals state) (seen : locals name = some entry)
    (owned : name ∈ block.owned) :
    ∃ address defining, Body.Evaluates block state (.scalar (.read name)) (Leaf.readOperand (fileSlot name))
      (.ok (.function address) state) ∧ Nonempty (ClosureAt entry.site entry.id defining state address) :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance.evaluated_local live seen owned

/-- An owned write transfers or clears the destination and preserves other tracked names. -/
theorem assigned_live {block : LexicalBlock} {locals : Locals block} {state middle : State} {name : String}
    {expression : Lowering.Resolve.SourceExpr} {code : Lowering.Expr} {entry : Option (Entry block)} {value : Lists.Value}
    (tracked : Tracks locals expression code entry)
    (ran : Body.Evaluates block state expression code (.ok value middle))
    (kept : Body.Keeps state.heap.size state middle)
    (live : Live locals state) (distinct : DistinctOwned state)
    {free : List FreeName} {floor : Nat} (frame : Body.Frame block free floor middle) (owned : name ∈ block.owned) :
    Live (setLocal locals name entry) (middle.write (fileSlot name) value) :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance.assigned_live tracked ran kept live distinct frame owned

/-- From the empty local provenance map, a checked suite derives its source trace and exact resolved outcome. -/
theorem runs {block : LexicalBlock} {source : Statement} {seed final : Program}
    {code : ResolvedBody} {emissions : Emissions} (profile : Elaborates block empty source seed code final emissions)
    {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (table : PreservesDeclarations final resolved.program)
    (available : List DeclarationId) (guarded : List.Subset (emissions.map Prod.fst) available)
    {before after : List Binding} {free : List FreeName} (selected : Selects block (before ++ code.reads ++ after) free)
    (state : State) {floor : Nat} (frame : Body.Frame block free floor state) (distinct : DistinctOwned state) :
    ∃ out, Runs block state source code.code out ∧ Body.Frame block free floor (finishState out) ∧
      Body.Keeps floor state (finishState out) ∧ Exec resolved.program available state code.code out ∧
      denoteBody resolved.program available code.code state = out :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance.runs profile checked table available guarded selected state frame distinct

/-- The reached activation provides fresh distinct locals and the original live capture cells. -/
theorem runs_activated {parent : LexicalBlock} {formals : List PlainKeywordParameter} (site : Site parent formals) {seed final : Program} {emissions : Emissions}
    (profile : Elaborates site.block empty site.source seed site.body final emissions)
    {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (table : PreservesDeclarations final resolved.program)
    (available : List DeclarationId) (guarded : List.Subset (emissions.map Prod.fst) available)
    (caller defining : State) (captures : List Capture) (installed : Installs defining site.free captures)
    (live : Body.CaptureCells caller captures) (assigned : List (Binding × Lists.Value)) :
    let active := activate caller site.declaration captures assigned
    ∃ out, Runs site.block active site.source site.body.code out ∧
      Body.Frame site.block site.free caller.heap.size (finishState out) ∧
      Body.Keeps caller.heap.size active (finishState out) ∧
      Exec resolved.program available active site.body.code out ∧
      denoteBody resolved.program available site.body.code active = out :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance.runs_activated site profile checked table available guarded caller defining captures installed live assigned

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance
