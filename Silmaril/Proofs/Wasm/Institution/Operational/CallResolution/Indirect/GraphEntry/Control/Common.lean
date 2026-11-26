module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Control.Defs
import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Control.Proofs

open Execution.Runtime (Frame Value)
open CallContinuation.OuterCall
open CallContinuation.OuterCall.Ranked
open Context.Resume (Block)

variable {entry : Entry} {program : Graph.Program} {tables : Source.Tables} {outer : Frame}
  {index : FuncIdx} {args : List Value}

theorem site_checked (ready : entry.Checked program tables outer index args) :
    entry.site.Checked program tables outer index args :=
  ⟨(Bool.and_eq_true_iff.mp ready.source).1, ready.found, ready.resolves, ready.typed⟩

private theorem locals_typed (ready : entry.Checked program tables outer index args) :
    (entry.site.frame args).locals.map Value.type = entry.cont.owner.localTypes := by
  simp [Entry.site, GraphEntry.Entry.frame, Declaration.frame, Graph.Function.localTypes,
    Function.comp_def, Value.zero, ready.typed]

private theorem read_choice (ready : entry.Checked program tables outer index args)
    {entered block choice} (checked : entry.choiceCheck entered block choice = true) :
    ∃ value, (entry.site.frame args).locals[choice.condition.toNat]? = some (.int .i32 value) := by
  have typed : entry.cont.owner.localTypes[choice.condition.toNat]? = some (.int .i32) :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp checked).1).1
  rw [← locals_typed ready, List.getElem?_map] at typed
  cases read : (entry.site.frame args).locals[choice.condition.toNat]? with
  | none => simp [read] at typed
  | some cell =>
    have ty : cell.type = .int .i32 := by simpa [read] using typed
    cases cell with
    | mk t bits =>
      change t = .int .i32 at ty
      subst t
      exact ⟨bits, rfl⟩

theorem trace_exists (ready : entry.Checked program tables outer index args) :
    ∃ states endpoint, entry.Trace args states endpoint := by
  have run (entered : List Block) (nodes : List Node) (checked : entry.checkNodes entered nodes = true) :
      ∃ states endpoint, Trace (entry.site.frame args).locals entered nodes states endpoint := by
    induction nodes generalizing entered with
    | nil => exact ⟨[], .site entered, .done entered⟩
    | cons node rest ih =>
      obtain ⟨localCheck, tailCheck⟩ := Bool.and_eq_true_iff.mp checked
      obtain ⟨states, endpoint, next⟩ := ih (entered ++ [node.block]) tailCheck
      rcases node with ⟨block, _ | choice⟩
      · exact ⟨_, endpoint, .block next⟩
      · obtain ⟨value, read⟩ := read_choice ready localCheck
        cases select : choice.takesSite value with
        | false => exact ⟨_, _, .alternate read select⟩
        | true => exact ⟨_, endpoint, .taken read select (.block next)⟩
  exact run [] entry.nodes (Bool.and_eq_true_iff.mp ready.source).2

private def Reaches (blocks : List Block) : Endpoint → Prop
  | .site entered => entered = blocks
  | .alternate .. => True

private theorem path_spine {locals entered nodes states result}
    (trace : Trace locals entered nodes states result) :
    Reaches (entered ++ nodes.map Node.block) result := by
  induction trace with
  | done => simp [Reaches]
  | block next ih => simpa [List.append_assoc] using ih
  | taken read select next ih => exact ih
  | alternate => trivial

theorem site_spine {locals entered nodes states blocks}
    (trace : Trace locals entered nodes states (.site blocks)) :
    blocks = entered ++ nodes.map Node.block :=
  path_spine trace

theorem scopes_append_one (blocks : List Block) (block : Block) (saved : List Value) :
    Block.scopes (blocks ++ [block]) saved =
      Block.scopes blocks saved ++ [block.scope (if blocks.isEmpty then saved else [])] := by
  induction blocks generalizing saved with
  | nil => rfl
  | cons head tail ih =>
    simp [Block.scopes, ih]

private theorem choice_admitted (ready : entry.Checked program tables outer index args)
    {entered block choice} (checked : entry.choiceCheck entered block choice = true) :
    Graph.Admitted program entry.cont.owner
      (entry.alternatePhase args entered (Node.alternateCode block choice)) := by
  obtain ⟨head, body⟩ := Bool.and_eq_true_iff.mp checked
  exact Context.Resume.plug_admitted entered entry.cont.owner.initial entry.cont.owner.declaration.results []
    (Bool.and_eq_true_iff.mp head).2 (.running (locals_typed ready) body)

private def AdmittedEnd (entry : Entry) (program : Graph.Program) (args : List Value) : Endpoint → Prop
  | .site _ => True
  | .alternate entered code => Graph.Admitted program entry.cont.owner (entry.alternatePhase args entered code)

theorem alternate_admitted (ready : entry.Checked program tables outer index args)
    {states entered code} (trace : entry.Trace args states (.alternate entered code)) :
    Graph.Admitted program entry.cont.owner (entry.alternatePhase args entered code) := by
  have sound {before nodes states end_}
      (path : Trace (entry.site.frame args).locals before nodes states end_)
      (checked : entry.checkNodes before nodes = true) :
      AdmittedEnd entry program args end_ := by
    induction path with
    | done => trivial
    | block next ih => exact ih (Bool.and_eq_true_iff.mp checked).2
    | taken read select next ih =>
      exact ih (Bool.and_eq_true_iff.mpr ⟨rfl, (Bool.and_eq_true_iff.mp checked).2⟩)
    | alternate read select => exact choice_admitted ready (Bool.and_eq_true_iff.mp checked).1
  exact sound trace (Bool.and_eq_true_iff.mp ready.source).2

theorem selected_arm {A : Type} (choice : Choice) (value : BitVec 32) (site alternate : A) :
    (if value = 0 then (choice.arms site alternate).2 else (choice.arms site alternate).1) =
      (if choice.takesSite value then site else alternate) := by
  cases arm : choice.siteOnTrue <;> by_cases zero : value = (0#32) <;>
    simp [Choice.arms, Choice.takesSite, arm, zero]

theorem trace_head {C : Type} (render : Position → C) (finish : Endpoint → C)
    (site : ∀ entered, finish (.site entered) = render (.pending entered []))
    {locals entered nodes states endpoint} (trace : Trace locals entered nodes states endpoint) :
    (states.map render ++ [finish endpoint]).head? = some (render (.pending entered nodes)) := by
  cases trace <;> simp [site]

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Control.Proofs
