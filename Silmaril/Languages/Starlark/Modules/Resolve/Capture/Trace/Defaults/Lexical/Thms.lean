module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Lexical.Defs
public import Silmaril.Languages.Starlark.Functions.Thms
public import Silmaril.Languages.Starlark.Functions.Expressions.Denotation.Defs
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Lexical.Eval

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Lexical

open Assignment (LexicalBlock)
open Functions
open Functions.Lowering.Resolve (resolveTracked)
open Lists (State Outcome)

/-- The lexical derivation predicts the checked compiler's operand and read order. -/
theorem translates {block : LexicalBlock} {source : List (String × Lowering.Resolve.SourceExpr)} {items : List PlainPositionalDefault}
    (related : Elaborates block source items) :
    items.map (fun item => (item.name, item.source)) = source ∧
      ∀ item ∈ items, resolveTracked block.context item.source = .ok (item.value, item.reads) :=
  ⟨Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Lexical.sources_eq related,
    Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Lexical.translated related⟩

/-- The definition-time expression sequence agrees on values or the first
error, including the reached heap. These operands do not dispatch calls. -/
theorem evaluates_agree (program : Program) (available : List DeclarationId)
    (bodyMeaning : Lowering.ClosureMeaning available) {block : LexicalBlock} {state : State}
    {items : List PlainPositionalDefault} {out : Outcome (List Lists.Value)}
    (ran : Evaluates block state items out) :
    (items.map PlainPositionalDefault.value).mapM (Lowering.denoteExprWith program available bodyMeaning) state = out :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Lexical.evaluates_agree
    program available bodyMeaning ran

/-- Evaluating the bounded operands only extends the heap and preserves
the defining slot map, including when a later operand fails. -/
theorem evaluates_keeps {block : LexicalBlock} {source : List (String × Lowering.Resolve.SourceExpr)}
    {items : List PlainPositionalDefault} (related : Elaborates block source items) {state : State}
    {result : Outcome (List Lists.Value)} (evaluated : Evaluates block state items result) :
    Body.Keeps state.heap.size state (Lists.Iteration.finishState result) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Lexical.evaluates_keeps related evaluated

/-- A reached definition agrees with native execution and denotation. The
installed environment can forward existing addresses from the defining frame. -/
theorem defines_agree (program : Program) (available : List DeclarationId) (target : Binding)
    (id : Nat) (parameters : Parameters) (declaration : Declaration)
    {block : LexicalBlock} {items : List PlainPositionalDefault}
    (related : Elaborates block parameters.optional items)
    (found : program[id]? = some declaration)
    (signature : declaration.signature = parameters.signature (items.map PlainPositionalDefault.value))
    {state : State} {out : Outcome Lists.Iteration.Flow}
    (source : Defines block target id declaration.free parameters items state out) :
    Exec program available state (.define target id) out ∧ denoteBody program available (.define target id) state = out :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Lexical.defines_sound
    program available target id parameters declaration related found signature source

/-- A checked lexical plan and the defining frame's addresses suffice
to construct the reached definition, including a first default error.
Forwarded addresses stay valid through the allocation-only operands. -/
theorem defines_total (program : Program) (available : List DeclarationId) (target : Binding)
    (id : Nat) (parameters : Parameters) (declaration : Declaration)
    {block : LexicalBlock} {items : List PlainPositionalDefault}
    (related : Elaborates block parameters.optional items)
    (found : program[id]? = some declaration)
    (signature : declaration.signature = parameters.signature (items.map PlainPositionalDefault.value))
    (state : State) (captures : List Lists.Capture)
    (installed : Installs state declaration.free captures) :
    ∃ out, Defines block target id declaration.free parameters items state out ∧
      Exec program available state (.define target id) out ∧ denoteBody program available (.define target id) state = out ∧
      (∀ next, out = .ok .next next → ∃ final values, Evaluates block state items (.ok values final) ∧
        next = install target id captures ((parameters.optional.map (fileSlot ∘ Prod.fst)).zip values) final) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Lexical.defines_total
    program available target id parameters declaration related found signature state captures installed

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Lexical
