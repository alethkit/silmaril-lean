module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Modules (fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence (PreservesDeclarations)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Capture Value)
open Silmaril.Languages.Starlark.Lists.Iteration (Flow)

theorem compiles {block : LexicalBlock} {source : Statement} {seed final : Program}
    {resolved : ResolvedBody} {emissions : Emissions}
    (profile : Elaborates block source seed resolved final emissions) :
    compileBody ⟨block.context, .local⟩ source seed = .ok (resolved, final) := by
  induction profile with
  | straight body => exact Body.compile_suite body _
  | define site leading _ _ child rest =>
    have ⟨same, tracked⟩ := Lexical.translates site.lexical
    have compiled := Body.compile_nested_body site.name site.parameters site.collects site.localOrder
      site.body site.selects site.defaults same tracked _ _ child
    exact Body.compile_prefix leading (compileBody_plainSeq _ _ _ _ _ _ _ _ compiled rest)

theorem collects {block : LexicalBlock} {source : Statement} {seed final : Program}
    {resolved : ResolvedBody} {emissions : Emissions}
    (profile : Elaborates block source seed resolved final emissions) :
    ∃ occurrences, Block.BodyBinders source occurrences := by
  induction profile with
  | straight => exact ⟨_, Body.collects _⟩
  | define site _ _ _ _ rest =>
    obtain ⟨_, tail⟩ := rest
    exact ⟨_, Body.collects_prefix _ (.seq (.define site.name site.parameters.source site.source) tail)⟩

theorem read_origins {block : LexicalBlock} {source : Statement} {seed final : Program}
    {resolved : ResolvedBody} {emissions : Emissions}
    (profile : Elaborates block source seed resolved final emissions) :
    ∀ binding ∈ resolved.reads, ∃ origin, ReadOrigin block binding origin := by
  induction profile with
  | straight body => exact Body.body_origins body
  | define site leading _ _ _ rest =>
    intro binding member
    rcases List.mem_append.mp member with earlier | remaining
    · exact Body.prefix_read_origins leading binding earlier
    · exact (List.mem_append.mp remaining).elim (Nested.definition_read_origins site.selects site.lexical binding)
        (rest binding)

theorem selects {block : LexicalBlock} {source : Statement} {seed final : Program}
    {resolved : ResolvedBody} {emissions : Emissions}
    (profile : Elaborates block source seed resolved final emissions) :
    ∃ free, Selects block resolved.reads free :=
  selects_of_origins block (read_origins profile)

private theorem push_preserves (program : Program) (declaration : Declaration) :
    PreservesDeclarations program (program.push declaration) := by
  intro id entry found
  have old := (Array.getElem?_eq_some_iff.mp found).choose
  simp [Array.getElem?_push, Nat.ne_of_lt old, found]

theorem links {block : LexicalBlock} {source : Statement} {seed final : Program}
    {resolved : ResolvedBody} {emissions : Emissions}
    (profile : Elaborates block source seed resolved final emissions) :
    PreservesDeclarations seed final ∧
      ∀ entry ∈ emissions, final[entry.1]? = some entry.2 := by
  induction profile with
  | straight => exact ⟨fun _ _ found => found, by simp⟩
  | define site _ _ _ child rest =>
    obtain ⟨start, childLinks⟩ := child
    obtain ⟨tailPreserves, tailLinks⟩ := rest
    have throughParent : PreservesDeclarations _ _ := fun id entry found =>
      tailPreserves id entry (push_preserves _ site.declaration id entry found)
    refine ⟨fun id entry found => throughParent id entry (start id entry found), ?_⟩
    intro entry present
    rcases List.mem_append.mp present with descendant | emittedLater
    · exact throughParent entry.1 entry.2 (childLinks entry descendant)
    · rcases List.mem_cons.mp emittedLater with rfl | inTail
      · exact tailPreserves _ _ Array.getElem?_push_size
      · exact tailLinks entry inTail

theorem indices {block : LexicalBlock} {source : Statement} {seed final : Program}
    {resolved : ResolvedBody} {emissions : Emissions}
    (profile : Elaborates block source seed resolved final emissions) :
    emissions.map Prod.fst = List.range' seed.size emissions.length ∧
      final.size = seed.size + emissions.length := by
  induction profile with
  | straight => simp
  | @define _ _ _ _ _ seed childTable final _ descendants remaining site _ _ _ child rest =>
    obtain ⟨childOrder, childSize⟩ := child
    obtain ⟨tailOrder, tailSize⟩ := rest
    constructor
    · simp only [List.map_append, List.map_cons, childOrder, tailOrder, List.length_append, List.length_cons]
      rw [← List.range'_append_1, Array.size_push, childSize, List.range'_succ]
    · simp only [List.length_append, List.length_cons, tailSize, Array.size_push, childSize]
      omega

private theorem requested {parent : LexicalBlock} (site : Site parent) (before after : List Binding)
    (entry : FreeName) (member : entry ∈ site.free) : entry.source ∈ before ++ site.reads ++ after := by
  have seen : entry.source ∈ site.reads := List.mem_append_right _ (List.mem_map.mpr ⟨_, member, rfl⟩)
  simp only [List.mem_append, seen, or_true, true_or]

theorem forwarding_request {parent : LexicalBlock} (site : Site parent)
    {before after : List Binding} {free : List FreeName}
    (selected : Selects parent (before ++ site.reads ++ after) free)
    (binding : Binding) (present : (⟨binding, binding⟩ : FreeName) ∈ site.free) :
    (⟨binding, binding⟩ : FreeName) ∈ free ↔ binding.scope = .global ∨ binding.name ∉ parent.owned := by
  rw [selected_member selected binding]
  exact and_iff_right (requested site before after _ present)

theorem installs {parent : LexicalBlock} (site : Site parent)
    {before after : List Binding} {free : List FreeName}
    (selected : Selects parent (before ++ site.reads ++ after) free)
    {state : State} {floor : Nat} (frame : Body.Frame parent free floor state) :
    ∃ captures, Installs state site.free captures ∧ Body.CaptureCells state captures := by
  exact Nested.installs_from_frame site.selects selected (requested site before after) frame

theorem activate_address {parent : LexicalBlock} (site : Site parent)
    {defining : State} {captures : List Capture} (installed : Installs defining site.free captures)
    (caller : State) (assigned : List (Binding × Value))
    (binding : Binding) (address : Nat) (present : (⟨binding, binding⟩ : FreeName) ∈ site.free)
    (origin : Forwarding.HasAddress defining binding address) :
    (activate caller site.declaration captures assigned).slots binding =
      some (.captured address (binding.scope == .local)) := by
  have codeLength : (site.defaults.map PlainPositionalDefault.value).length = site.parameters.optional.length := by
    simpa using congrArg List.length (Lexical.translates site.lexical).1
  exact Nested.activate_address site.selects (Body.signature_slots site.parameters site.locals _ codeLength)
    installed caller assigned binding address present origin

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
          ((site.parameters.optional.map (fileSlot ∘ Prod.fst)).zip values) evaluated) := by
  obtain ⟨captures, installed, live⟩ := installs site selected frame
  obtain ⟨out, ran, exec, meaning, saved⟩ :=
    Lexical.defines_total program available (fileSlot site.name) id site.parameters site.declaration
      site.lexical found rfl state captures installed
  exact ⟨captures, out, installed, live, ran, exec, meaning, saved⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive
