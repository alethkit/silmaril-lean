module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Lexical.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Reached

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested

open Assignment (LexicalBlock)
open Functions
open Lists (State)

local notation "Source" => Body.Definition

/-- Independent binder and operand derivations determine the ordered
child layout and free references. -/
theorem plan_of_body {parent : LexicalBlock} {source : Source} (target : source.name ∈ parent.owned)
    {locals : List String} (binders : Block.LocalBinders source.parameters.names source.body.binders locals)
    {code : Functions.Body} {reads : List Binding}
    (body : Body.Elaborates ⟨source.parameters.names ++ locals, parent.owned ++ parent.enclosing,
      parent.globals⟩ source.body code reads)
    {items : List PlainPositionalDefault} (defaults : Lexical.Elaborates parent source.parameters.optional items) :
    Nonempty (Plan parent source) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.plan_of_body target binders body defaults

/-- The child is emitted at the next code-table index. Its defining
block receives both categories of read demands in source order. -/
theorem compile_definition {parent : LexicalBlock} {source : Source} (plan : Plan parent source) (seed : Program) :
    compileBody ⟨parent.context, .local⟩ (statement source) seed =
      .ok (⟨.define (fileSlot source.name) seed.size, plan.reads⟩, seed.push plan.declaration) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.compile_definition plan seed

/-- The child's definition-site demands can be inserted among the
parent's other reads to derive the parent's own ordered capture list. -/
theorem selects_parent {parent : LexicalBlock} {source : Source} (plan : Plan parent source)
    {before after : List Binding}
    (surrounding : ∀ binding ∈ before ++ after, ∃ origin, ReadOrigin parent binding origin) :
    ∃ free, Selects parent (before ++ plan.reads ++ after) free :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.selects_parent plan surrounding

/-- Select the child's captures from the reached parent frame. A local
declared in the parent supplies its owned address. Other requests use
the inherited slot, retaining its address and local or module tag. -/
theorem installs {parent : LexicalBlock} {source : Source} (plan : Plan parent source)
    {before after : List Binding} {parentFree : List FreeName}
    (selected : Selects parent (before ++ plan.reads ++ after) parentFree)
    {state : State} {floor : Nat} (frame : Body.Frame parent parentFree floor state) :
    ∃ captures, Installs state plan.body.free captures ∧ Body.CaptureCells state captures :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.installs plan selected frame

/-- When the parent already forwarded a local, activating the child
with the derived vector keeps that same address across caller changes. -/
theorem activate_forwarded {parent : LexicalBlock} {source : Source} (plan : Plan parent source)
    {state : State} {captures : List Lists.Capture} (installed : Installs state plan.body.free captures)
    (caller : State) (assigned : List (Binding × Lists.Value)) (name : String) (address : Nat)
    (present : (⟨fileSlot name, fileSlot name⟩ : FreeName) ∈ plan.body.free)
    (forwarded : state.slots (fileSlot name) = some (.captured address true)) :
    (activate caller plan.declaration captures assigned).slots (fileSlot name) = some (.captured address true) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.activate_forwarded plan installed
    caller assigned name address present forwarded

/-- At a reached nested definition, the compiled declaration, full
parent selection, and frame invariant suffice to derive the capture
vector and the independent definition step. -/
theorem reached {parent : LexicalBlock} {source : Source} (plan : Plan parent source)
    {before after : List Binding} {parentFree : List FreeName}
    (selected : Selects parent (before ++ plan.reads ++ after) parentFree)
    (program : Program) (available : List DeclarationId) (id : DeclarationId)
    (found : program[id]? = some plan.declaration) {state : State} {floor : Nat}
    (frame : Body.Frame parent parentFree floor state) :
    ∃ captures out, Installs state plan.body.free captures ∧ Body.CaptureCells state captures ∧
      Lexical.Defines parent (fileSlot source.name) id plan.body.free source.parameters plan.defaults state out ∧
      Exec program available state (.define (fileSlot source.name) id) out ∧
      denoteBody program available (.define (fileSlot source.name) id) state = out ∧
      DefinitionResult plan id captures state out :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.reached plan selected
    program available id found frame

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested
