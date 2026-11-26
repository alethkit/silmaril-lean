module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Modules (fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (Outcome State)
open Silmaril.Languages.Starlark.Lists.Iteration (Flow finishState)

theorem compiles {block : LexicalBlock} {source : Statement} {seed final : Program} {resolved : ResolvedBody}
    (profile : Elaborates block source seed resolved final) :
    compileBody ⟨block.context, .local⟩ source seed = .ok (resolved, final) := by
  induction profile with
  | straight body => exact Body.compile_suite body _
  | define leadingProfile plan _ ih =>
    exact Body.compile_prefix leadingProfile
      (compileBody_plainSeq _ _ _ _ _ _ _ _ (Nested.compile_definition plan _) ih)

theorem collects {block : LexicalBlock} {source : Statement} {seed final : Program} {resolved : ResolvedBody}
    (profile : Elaborates block source seed resolved final) :
    ∃ occurrences, Block.BodyBinders source occurrences := by
  induction profile with
  | straight => exact ⟨_, Body.collects _⟩
  | define _ _ _ ih =>
    obtain ⟨_, tail⟩ := ih
    exact ⟨_, Body.collects_prefix _ (.seq (.define _ _ _) tail)⟩

theorem preserves_declarations {block : LexicalBlock} {source : Statement}
    {seed final : Program} {resolved : ResolvedBody}
    (profile : Elaborates block source seed resolved final) :
    PreservesDeclarations seed final := by
  induction profile with
  | straight => exact fun _ _ found => found
  | define _ _ _ ih =>
    intro id declaration found
    have old := (Array.getElem?_eq_some_iff.mp found).choose
    exact ih id declaration (by simp [Array.getElem?_push, Nat.ne_of_lt old, found])

theorem selects {block : LexicalBlock} {source : Statement} {seed final : Program} {resolved : ResolvedBody}
    (profile : Elaborates block source seed resolved final) :
    ∃ free, Selects block resolved.reads free := by
  apply selects_of_origins
  induction profile with
  | straight body => exact Body.body_origins body
  | define leadingProfile plan _ ih =>
    intro binding seen
    rcases List.mem_append.mp seen with leading | remaining
    · exact Body.prefix_read_origins leadingProfile binding leading
    · exact (List.mem_append.mp remaining).elim (Nested.read_origins plan binding) (ih binding)

private theorem keeps_trans {floor : Nat} {first middle last : State}
    (head : Body.Keeps floor first middle) (tail : Body.Keeps floor middle last) :
    Body.Keeps floor first last :=
  ⟨tail.1.trans head.1, fun key cell low stored => tail.2 key cell low (head.2 key cell low stored)⟩

theorem runs {block : LexicalBlock} {source : Statement} {seed final : Program} {resolved : ResolvedBody}
    (profile : Elaborates block source seed resolved final) (program : Program)
    (linked : PreservesDeclarations final program) (available : List DeclarationId)
    {before after : List Binding} {free : List FreeName}
    (selection : Selects block (before ++ resolved.reads ++ after) free) (state : State) {floor : Nat}
    (frame : Body.Frame block free floor state) :
    ∃ out, Runs block state source resolved.code out ∧ Body.Frame block free floor (finishState out) ∧
      Body.Keeps floor state (finishState out) ∧ Exec program available state resolved.code out ∧
      denoteBody program available resolved.code state = out := by
  induction profile generalizing state before after with
  | straight body =>
    obtain ⟨out, ran, reached, kept, native, meaning⟩ := Body.body_agrees program available body state frame
    exact ⟨out, .straight ran, reached, kept, native, meaning⟩
  | @define leading leadingCode leadingReads child rest seed final tail leadingProfile plan remaining ih =>
    let first : Body := .define (fileSlot child.name) seed.size
    let continuation := Body.seq first tail.code
    obtain ⟨prefixOut, ranPrefix, entered, keptPrefix⟩ := Body.prefix_total leadingProfile state frame
    have prefixSound (out : Outcome Flow)
        (cont : ∀ active, prefixOut = .ok () active → Exec program available active continuation out) :=
      Body.prefix_agrees program available ranPrefix continuation out
        (fun active outcome => (exec_iff_denoteBody _ _ _ _ _).mp (cont active outcome))
    cases prefixOut with
    | error error stopped =>
      obtain ⟨native, meaning⟩ := prefixSound (.error error stopped) (fun _ impossible => nomatch impossible)
      exact ⟨_, .prefixError ranPrefix, entered, keptPrefix, native, meaning⟩
    | ok result active =>
      cases result
      have found := linked _ _ (preserves_declarations remaining _ _ Array.getElem?_push_size)
      have selectedDefinition : Selects block ((before ++ leadingReads) ++ plan.reads ++ (tail.reads ++ after)) free := by
        simpa only [List.append_assoc] using selection
      obtain ⟨captures, definitionOut, captured, _, _, definitionExec, _, defined⟩ :=
        Nested.reached plan selectedDefinition program available seed.size found entered
      have ⟨afterDefinition, keptDefinition⟩ := Nested.result_frame plan entered defined
      cases definitionOut with
      | error error stopped =>
        obtain ⟨native, meaning⟩ := prefixSound (.error error stopped)
          (fun _ eq => by cases eq; exact .seqError definitionExec)
        exact ⟨_, .definitionError ranPrefix defined, afterDefinition, keeps_trans keptPrefix keptDefinition, native, meaning⟩
      | ok signal installed =>
        have next : signal = .next := by cases defined; rfl
        subst signal
        have selectedTail : Selects block ((before ++ leadingReads ++ plan.reads) ++ tail.reads ++ after) free := by
          simpa only [List.append_assoc] using selection
        obtain ⟨out, ranTail, reached, keptTail, nativeTail, _⟩ := ih linked selectedTail installed afterDefinition
        obtain ⟨native, meaning⟩ := prefixSound out (fun _ eq => by cases eq; exact .seq definitionExec nativeTail)
        exact ⟨out, .define ranPrefix captured defined ranTail, reached,
          keeps_trans keptPrefix (keeps_trans keptDefinition keptTail), native, meaning⟩

theorem installation {block : LexicalBlock} {child : Body.Definition} (plan : Nested.Plan block child)
    {id : DeclarationId} {captures : List Silmaril.Languages.Starlark.Lists.Capture} {start installed : State}
    (result : Nested.DefinitionResult plan id captures start (.ok .next installed)) :
    Nonempty (Installed plan id captures installed) := by
  cases result with
  | installed evaluated _ bound recorded =>
    exact ⟨⟨_, _, Lexical.evaluated_length plan.lexical evaluated, bound, recorded⟩⟩

theorem prepare_installed {block : LexicalBlock} {child : Body.Definition}
    {plan : Nested.Plan block child} {id : DeclarationId} {captures : List Silmaril.Languages.Starlark.Lists.Capture}
    {installed : State} (origin : Installed plan id captures installed)
    {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (found : resolved.program[id]? = some plan.declaration)
    (later : State) (frozen : Bool) (actuals : List Silmaril.Languages.Starlark.Lists.Value)
    (recorded : later.heap[origin.address]? = some ⟨.function ⟨id, captures,
      (child.parameters.optional.map (fileSlot ∘ Prod.fst)).zip origin.values⟩, frozen⟩) :
    let available := List.range resolved.program.size
    ∃ result, Binds (child.parameters.slots origin.values) actuals result ∧
      ∃ permitted : id ∈ available,
        prepareExpanded resolved.program available ⟨actuals, []⟩ (.function origin.address) later =
          match result with
          | .error error => .error error later
          | .ok assigned => .ok (.closure ⟨id, permitted, plan.declaration.body⟩)
            (activate later plan.declaration captures assigned) := by
  have same := (Lexical.translates plan.lexical).1
  have length : (plan.defaults.map PlainPositionalDefault.value).length = child.parameters.optional.length := by
    simpa using congrArg List.length same
  obtain ⟨result, bound⟩ := Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.binds_total (child.parameters.slots origin.values) actuals
  have prepared := Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.checked_prepare_signature
    checked id child.parameters plan.declaration _ found rfl length later origin.address frozen
    captures origin.values actuals origin.length recorded bound
  refine ⟨result, bound, ?_⟩
  cases result <;> exact prepared

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence
