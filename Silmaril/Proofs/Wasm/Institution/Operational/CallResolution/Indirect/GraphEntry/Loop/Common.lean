module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Defs
import Silmaril.Wasm.Institution.Operational.Locals.Thms
import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Proofs

open Execution.Runtime (Frame Value)
open CallContinuation.OuterCall
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked

variable {entry : Entry} {program : Graph.Program} {tables : Source.Tables} {outer : Frame}
  {index : FuncIdx} {args : List Value}

theorem graph_checked (ready : entry.Checked program tables outer index args) :
    program.checkDirect = true :=
  (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ready.source).1).1).1).1).1

private theorem flags (ready : entry.Checked program tables outer index args) :
    ∀ i ∈ [entry.restart, entry.nextRestart, entry.choose], entry.owner.localTypes[i.toNat]? = some (.int .i32) := by
  have checked := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ready.source).1).1).1).1).2
  intro i member
  exact of_decide_eq_true ((List.all_eq_true.mp checked) i member)

theorem void_result (ready : entry.Checked program tables outer index args) : entry.result = none := by
  have onlyVoid := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ready.source).1).1).1).2
  cases result : entry.result with
  | none => rfl
  | some t => simp [result] at onlyVoid

theorem caller_admitted (ready : entry.Checked program tables outer index args)
    {locals} (typed : entry.Typed ⟨locals, .caller⟩) :
    Graph.Admitted program entry.owner (entry.callerPhase locals) := by
  apply Graph.AdmittedAt.running typed
  have checked := (Bool.and_eq_true_iff.mp ready.source).2
  simpa [Graph.Function.WellTyped, void_result ready] using checked

theorem initial_typed (ready : entry.Checked program tables outer index args) :
    entry.Typed (entry.initial args) := by
  simp [Entry.Typed, Entry.initial, Declaration.frame, Graph.Function.localTypes, Function.comp_def, Value.zero, ready.typed]

private theorem read_i32 {types : List NumType} {locals : List Value} {i : LocalIdx}
    (typed : locals.map Value.type = types) (slot : types[i.toNat]? = some (.int .i32)) :
    ∃ value, locals[i.toNat]? = some (.int .i32 value) := by
  rw [← typed, List.getElem?_map] at slot
  cases read : locals[i.toNat]? with
  | none => simp [read] at slot
  | some cell =>
    have ty : cell.type = .int .i32 := by simpa [read] using slot
    cases cell with
    | mk t bits =>
      change t = .int .i32 at ty
      subst t
      exact ⟨bits, rfl⟩

theorem preserve (ready : entry.Checked program tables outer index args)
    {a b : State} (typed : entry.Typed a) (edge : Edge entry a b) : entry.Typed b := by
  cases edge <;> try exact typed
  case writeRestart locals nextLocals old next write =>
    have restartType := flags ready entry.restart (by simp)
    have guard : Locals.Admitted entry.owner.localTypes [] ⟨locals, [.value (.int .i32 next), .set entry.restart]⟩ :=
      ⟨typed, by simp [Locals.check, Value.int, restartType]⟩
    exact (Locals.closed guard write).1

theorem progress (ready : entry.Checked program tables outer index args)
    {a : State} (typed : entry.Typed a) (pending : a.phase.Pending) : ∃ b, Edge entry a b := by
  rcases a with ⟨locals, phase⟩
  cases phase with
  | enter => exact ⟨_, .enter⟩
  | readRestart =>
    obtain ⟨old, read⟩ := read_i32 typed (flags ready entry.restart (by simp))
    exact ⟨_, .readRestart read⟩
  | readNext old =>
    obtain ⟨next, read⟩ := read_i32 typed (flags ready entry.nextRestart (by simp))
    exact ⟨_, .readNext read⟩
  | writeRestart old next =>
    obtain ⟨_, read⟩ := read_i32 typed (flags ready entry.restart (by simp))
    exact ⟨_, .writeRestart (Locals.fact (.set _ _ _ (List.getElem?_eq_some_iff.mp read).1))⟩
  | testRestart old => exact ⟨_, .testRestart⟩
  | branch => exact ⟨_, .restart⟩
  | readChoice =>
    obtain ⟨value, read⟩ := read_i32 typed (flags ready entry.choose (by simp))
    exact ⟨_, .readChoice read⟩
  | testChoice value => exact ⟨_, .testChoice⟩
  | arm site =>
    cases site
    · exact ⟨_, .enterEmpty⟩
    · exact ⟨_, .enterSite⟩
  | emptyArm => exact ⟨_, .leaveEmpty⟩
  | exitLoop => exact ⟨_, .leaveLoop⟩
  | site | caller => exact pending.elim

theorem observe {C : Type} {entry : Entry} {args : List Value} (render : State → C) (native : C → C → Prop)
    (caller : List Value → C → Prop)
    (typed : entry.Typed (entry.initial args))
    (keeps : ∀ {a b}, entry.Typed a → Edge entry a b → entry.Typed b)
    (step : ∀ {a dst}, entry.Typed a → a.phase.Pending →
      (native (render a) dst ↔ ∃ b, Edge entry a b ∧ dst = render b))
    (tail : ∀ {locals dst}, entry.Typed ⟨locals, .caller⟩ →
      (Relation.ReflTransGen native (render ⟨locals, .caller⟩) dst ↔ caller locals dst))
    (dst : C) :
    Relation.ReflTransGen native (render (entry.initial args)) dst ↔
      Observation entry args render caller native dst := by
  have typedRun {b} (run : Runs entry (entry.initial args) b) : entry.Typed b := by
    induction run with
    | refl => exact typed
    | tail _ move ih => exact keeps ih move
  have sound {b} (run : Runs entry (entry.initial args) b) :
      Relation.ReflTransGen native (render (entry.initial args)) (render b) := by
    induction run with
    | refl => exact .refl
    | @tail current _ before move ih =>
      have live : current.phase.Pending := by cases move <;> trivial
      exact ih.tail ((step (typedRun before) live).mpr ⟨_, move, rfl⟩)
  constructor
  · intro path
    induction path with
    | refl => exact .inl ⟨_, .refl, rfl⟩
    | tail _ move ih =>
      rcases ih with ⟨state, run, rfl⟩ | ⟨locals, run, continues⟩ | ⟨locals, run, continues⟩
      · have valid := typedRun run
        rcases state with ⟨locals, phase⟩
        cases phase with
        | site => exact .inr (.inr ⟨_, run, Relation.ReflTransGen.single move⟩)
        | caller => exact .inr (.inl ⟨_, run, (tail valid).mp (Relation.ReflTransGen.single move)⟩)
        | _ =>
          obtain ⟨next, edge, eq⟩ := (step valid trivial).mp move
          exact .inl ⟨next, run.tail edge, eq⟩
      · exact .inr (.inl ⟨locals, run, (tail (typedRun run)).mp (((tail (typedRun run)).mpr continues).tail move)⟩)
      · exact .inr (.inr ⟨locals, run, continues.tail move⟩)
  · rintro (⟨state, run, rfl⟩ | ⟨locals, run, continues⟩ | ⟨locals, run, continues⟩)
    · exact sound run
    · exact (sound run).trans ((tail (typedRun run)).mpr continues)
    · exact (sound run).trans continues

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Proofs
