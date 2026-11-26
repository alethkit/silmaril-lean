module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Elaboration

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive

open Assignment (LexicalBlock)
open Functions (FreeName Program DeclarationId Exec activate denoteBody)
open Lists (State Capture Outcome)
open Lists.Iteration (Flow)

/-- Independent recursive elaboration agrees with the normalized compiler. -/
theorem compiles {block : LexicalBlock} {source : Statement} {seed final : Program}
    {resolved : ResolvedBody} {emissions : Emissions}
    (profile : Elaborates block source seed resolved final emissions) :
    compileBody ⟨block.context, .local⟩ source seed = .ok (resolved, final) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.compiles profile

theorem collects {block : LexicalBlock} {source : Statement} {seed final : Program}
    {resolved : ResolvedBody} {emissions : Emissions}
    (profile : Elaborates block source seed resolved final emissions) :
    ∃ occurrences, Block.BodyBinders source occurrences :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.collects profile

/-- Reads from nested definitions contribute to the enclosing free
references through their ordered demands, even without a direct read. -/
theorem selects {block : LexicalBlock} {source : Statement} {seed final : Program}
    {resolved : ResolvedBody} {emissions : Emissions}
    (profile : Elaborates block source seed resolved final emissions) :
    ∃ free, Selects block resolved.reads free :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.selects profile

/-- Every emission has the same lookup after any later sibling or
enclosing definition has been appended. The incoming table is preserved. -/
theorem links {block : LexicalBlock} {source : Statement} {seed final : Program}
    {resolved : ResolvedBody} {emissions : Emissions}
    (profile : Elaborates block source seed resolved final emissions) :
    PreservesDeclarations seed final ∧ ∀ entry ∈ emissions, final[entry.1]? = some entry.2 :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.links profile

theorem indices {block : LexicalBlock} {source : Statement} {seed final : Program}
    {resolved : ResolvedBody} {emissions : Emissions}
    (profile : Elaborates block source seed resolved final emissions) :
    emissions.map Prod.fst = List.range' seed.size emissions.length ∧ final.size = seed.size + emissions.length :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.indices profile

/-- A child's free reference needs forwarding exactly when it is
global or the parent does not own that local name. -/
theorem forwarding_request {parent : LexicalBlock} (site : Site parent)
    {before after : List Binding} {free : List FreeName}
    (selected : Selects parent (before ++ site.reads ++ after) free)
    (binding : Binding) (present : (⟨binding, binding⟩ : FreeName) ∈ site.free) :
    (⟨binding, binding⟩ : FreeName) ∈ free ↔ binding.scope = .global ∨ binding.name ∉ parent.owned :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.forwarding_request
    site selected binding present

theorem installs {parent : LexicalBlock} (site : Site parent)
    {before after : List Binding} {free : List FreeName}
    (selected : Selects parent (before ++ site.reads ++ after) free)
    {state : State} {floor : Nat} (frame : Body.Frame parent free floor state) :
    ∃ captures, Installs state site.free captures ∧ Body.CaptureCells state captures :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.installs site selected frame

/-- Along a forwarded edge the child's activation keeps the exact address
supplied by the defining frame. An owning frame can instead supply its
shadowing cell. This is independent of the size of the child's body. -/
theorem activate_address {parent : LexicalBlock} (site : Site parent)
    {defining : State} {captures : List Capture} (installed : Installs defining site.free captures)
    (caller : State) (assigned : List (Binding × Lists.Value))
    (binding : Binding) (address : Nat) (present : (⟨binding, binding⟩ : FreeName) ∈ site.free)
    (origin : Forwarding.HasAddress defining binding address) :
    (activate caller site.declaration captures assigned).slots binding =
      some (.captured address (binding.scope == .local)) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.activate_address
    site installed caller assigned binding address present origin

/-- Reaching a recursively elaborated definition still uses the same
lexical defaults and capture installation rule. The child body only
runs when its closure is invoked. -/
theorem reached {parent : LexicalBlock} (site : Site parent)
    {before after : List Binding} {free : List FreeName}
    (selected : Selects parent (before ++ site.reads ++ after) free)
    (program : Program) (available : List DeclarationId) (id : DeclarationId)
    (found : program[id]? = some site.declaration) {state : State} {floor : Nat}
    (frame : Body.Frame parent free floor state) :
    ∃ captures out, Installs state site.free captures ∧ Body.CaptureCells state captures ∧
      Lexical.Defines parent (fileSlot site.name) id site.free site.parameters site.defaults state out ∧
      Exec program available state (.define (fileSlot site.name) id) out ∧
      denoteBody program available (.define (fileSlot site.name) id) state = out ∧
      (∀ next, out = .ok .next next → ∃ evaluated values,
        Lexical.Evaluates parent state site.defaults (.ok values evaluated) ∧
        next = install (fileSlot site.name) id captures
          ((site.parameters.optional.map (fileSlot ∘ Prod.fst)).zip values) evaluated) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.reached
    site selected program available id found frame

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive
