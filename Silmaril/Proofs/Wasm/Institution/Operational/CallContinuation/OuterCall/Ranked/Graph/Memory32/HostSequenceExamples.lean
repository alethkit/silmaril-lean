module

import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Host.Sequence.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Thms
import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Thms

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.HostEntry.SequenceExamples

open Execution.Runtime (Frame FuncAddr HostOutcome MemAddr MemInst ModuleInst Value)
open Computed
open Wasm.V1.Execution

private abbrev i32 := Value.int .i32
private def slot : MemAddr := ⟨0⟩
private def rootAddr : FuncAddr := ⟨2⟩
private def hostType : Wasm.V1.FuncType := ⟨[.int .i32], [.int .i32]⟩
private def first : HostCall.V1.Site Nat := ⟨⟨0⟩, ⟨0⟩, hostType, 11⟩
private def second : HostCall.V1.Site Nat := ⟨⟨1⟩, ⟨1⟩, hostType, 19⟩
private def mod : ModuleInst := { funcs := [first.address, second.address], memories := [slot], types := [hostType] }
private def fn : Function :=
  ⟨⟨mod, ⟨0⟩, hostType.params, [.int .i32], hostType.results⟩, 0, [i32 0],
    [.ranked (.set ⟨1⟩), .load 1]⟩
private def segment : HostSegment Nat := ⟨[], second⟩
private def seq : Sequence Nat := ⟨⟨⟨0⟩, rootAddr, fn, [.get ⟨0⟩], first⟩, [segment]⟩
private def graph : Program := ⟨[], none⟩
private def rootArgs : List Value := [i32 5]
private def saved : List Value := [i32 0]
private def caller : Frame := ⟨[i32 42], { funcs := [rootAddr] }⟩
private def initial : MemInst := ⟨⟨#[0xaa, 0, 0, 0, 0, 0xbb]⟩, none⟩
private def base : Store Nat :=
  { funcs := [.host hostType 11, .host hostType 19, .wasm fn.declaration.type mod seq.v1Func],
    memories := [initial] }

private def live (bytes : ByteArray) := storeWithBytes base slot initial bytes
private def firstBytes : Bool → ByteArray
  | false => ⟨#[0xaa, 0x44, 0x33, 0x22, 0x11, 0xbb]⟩
  | true => ⟨#[0xaa, 0x88, 0x77, 0x66, 0x55, 0xbb]⟩
private def firstValue (choice : Bool) : Value := i32 (if choice then 8 else 7)
private def secondValue : Value := i32 100
private def word (choice : Bool) : BitVec 32 := if choice then 0x55667788 else 0x11223344

private inductive FirstOutcome : HostOutcome Wasm.V1.Func Nat → Prop
  | value (choice : Bool) : FirstOutcome (.returned (live (firstBytes choice)) (.values [firstValue choice]))
  | trap : FirstOutcome (.returned (live (firstBytes true)) .trap)

private def host : HostSemantics Nat :=
  fun id store input outcome =>
    (id = first.target ∧ store = live initial.data ∧ input = rootArgs ∧ FirstOutcome outcome) ∨
    ∃ choice : Bool, id = second.target ∧ store = live (firstBytes choice) ∧ input = [firstValue choice] ∧
      (outcome = .returned store (.values [secondValue]) ∨ outcome = .diverged)

private theorem isSite {site : HostCall.V1.Site Nat} (member : site ∈ seq.sites) : site = first ∨ site = second := by
  change site ∈ [first, second] at member
  simpa using member

private theorem checked : seq.Checked .fixed graph slot .ranked base caller rootArgs where
  resolved := rfl
  allocated := rfl
  parameters := rfl
  scalar := by decide
  slot := rfl
  linkedHosts := by
    intro site used
    rcases isSite used with rfl | rfl <;> exact ⟨rfl, rfl, by decide⟩
  typedBody := rfl
  supportedTail := rfl
  linkedTail := by intro _ h; cases h

private theorem layout : Layout graph base slot initial where
  memory := rfl
  functions := by intro _ _ h; simp [graph, Program.lookup] at h

private theorem contract : seq.Contract host .fixed slot initial base := by
  intro site used bytes _ input _ after result behavior
  have signature : site.signature = hostType := by rcases isSite used with rfl | rfl <;> rfl
  rcases behavior with ⟨_, store, _, behavior⟩ | ⟨choice, _, store, _, outcome | impossible⟩
  · rw [store]
    cases behavior with
    | value choice =>
      refine ⟨?_, initial.data, firstBytes choice, rfl, ?_, ?_⟩
      · rw [signature]
        rfl
      · cases choice <;> rfl
      · cases choice <;> rfl
    | trap => exact ⟨trivial, initial.data, firstBytes true, rfl, rfl, rfl⟩
  · cases outcome
    rw [store, signature]
    cases choice
    · exact ⟨rfl, firstBytes false, firstBytes false, rfl, rfl, rfl⟩
    · exact ⟨rfl, firstBytes true, firstBytes true, rfl, rfl, rfl⟩
  · cases impossible

private abbrev Phase := Sequence.Phase Nat
private abbrev Ready := seq.Ready .fixed graph slot .ranked initial
private abbrev Runs := seq.Runs host .fixed graph slot base initial initial.data caller rootArgs
private abbrev cfg := seq.render base slot initial initial.data caller rootArgs

private def source : Config Nat := ⟨live initial.data, caller, values rootArgs ++ [.source (.call ⟨0⟩)]⟩
private def firstPending : Phase := .pending initial.data saved rootArgs first [segment]
private def secondPending (choice : Bool) : Phase :=
  .pending (firstBytes choice) saved [firstValue choice] second []

private theorem correspondence {dst : Config Nat} :
    Steps host source dst ↔ ∃ phase, Runs .call phase ∧ Ready phase ∧ dst = cfg phase :=
  Sequence.v1_call_run_iff rfl checked layout trivial rfl contract

private theorem readyOnRun {phase : Phase} (run : Runs .call phase) : Ready phase := by
  induction run with
  | refl => trivial
  | tail _ move ih => exact move.ready rfl checked layout rfl contract ih

private theorem native {phase : Phase} (run : Runs .call phase) : Steps host source (cfg phase) :=
  correspondence.mpr ⟨phase, run, readyOnRun run, rfl⟩

private theorem firstRun : Runs .call firstPending :=
  (((Relation.ReflTransGen.single .resolve).tail .enter).tail (.numeric (.get rfl))).tail (.hostResolve rfl)

private theorem secondRun (choice : Bool) : Runs .call (secondPending choice) := by
  have delivered : Runs .call (seq.delivered caller rootArgs (firstBytes choice) saved [segment]
      (.values [firstValue choice])) :=
    firstRun.tail (.returned (.inl ⟨rfl, rfl, rfl, .value choice⟩) rfl)
  exact delivered.tail (.hostResolve rfl)

private def active : Frame := fn.declaration.frame rootArgs
private def recorded : Frame := { active with locals := rootArgs ++ [secondValue] }
private def framed (s : Store Nat) (f : Frame) (body : List Admin) : Config Nat :=
  ⟨s, caller, [.frame 1 f [.label 1 [] body]]⟩

-- Both outcomes from one first invocation feed the ordered value and the
-- actual returned store into the second native invocation.
example (choice : Bool) : Steps host source
    (framed (live (firstBytes choice)) active (values (saved ++ [firstValue choice]) ++ [.invoke second.address] ++ seq.root.tail)) :=
  native (secondRun choice)

private theorem nativeSuccess (choice : Bool) :
    Steps host source ⟨live (firstBytes choice), caller, values [i32 (word choice)]⟩ := by
  let store := live (firstBytes choice)
  let load : Admin := .source ((Op.load 1).v1)
  have delivered : Step host (cfg (secondPending choice))
      (framed store active (values saved ++ values [secondValue] ++ seq.root.tail)) :=
    .frame (.label (.context
      (.invokeHost store store active second.address hostType 19 [firstValue choice] (.values [secondValue])
        rfl rfl (.inr ⟨choice, rfl, rfl, rfl, .inl rfl⟩)) saved seq.root.tail) 1 []) 1 caller
  have recordedLocal : Step host (framed store active (values saved ++ values [secondValue] ++ seq.root.tail))
      (framed store recorded (values saved ++ [load])) :=
    .frame (.label (.context (.localSet store active ⟨1⟩ secondValue (i32 0) rfl) saved [load]) 1 []) 1 caller
  have read : Step host (framed store recorded (values saved ++ [load]))
      (framed store recorded (values [i32 (word choice)])) := by
    apply Step.frame (Step.label ?_ 1 []) 1 caller
    refine (MemoryWrite.v1_context_load_step_iff_at (immediate := immediate 1) (address := 0) (saved := [])
      (tail := []) (show frameMemory store recorded = some (slot, { initial with data := firstBytes choice }) from rfl)).mpr
      ⟨.value (word choice), ?_, rfl⟩
    cases choice <;> exact MemoryQuery.fact_at (.load _ _ (by decide))
  exact ((((native (secondRun choice)).tail delivered).tail recordedLocal).tail read
    |>.tail (.frame (.pure _ _ (.labelDone 1 [] [i32 (word choice)])) 1 caller))
    |>.tail (.pure _ _ (.frameDone 1 recorded [i32 (word choice)] rfl))

example (choice : Bool) :=
  correspondence.mp (nativeSuccess choice)

-- Declared divergence at the second invocation leaves the new store and the
-- pending invocation exactly in place.
example (choice : Bool) : Steps host source (cfg (secondPending choice)) :=
  native ((secondRun choice).tail (.diverged (.inr ⟨choice, rfl, rfl, rfl, .inr rfl⟩)))

private def afterTrap : Phase := .trapped (firstBytes true) saved (seq.continuation [segment])

private theorem trapDelivery : Runs .call afterTrap := by
  have returned : host first.target (live initial.data) rootArgs (.returned (live (firstBytes true)) .trap) :=
    .inl ⟨rfl, rfl, rfl, .trap⟩
  exact firstRun.tail (.returned returned rfl)

example : Steps host source (framed (live (firstBytes true)) active
    (values saved ++ .trap :: .source (.call second.index) :: seq.root.tail)) :=
  native trapDelivery

-- The next site's instruction is discarded on unwind. The trapping host's
-- returned bytes are still the live memory after the frame is discarded.
example : Steps host source ⟨live (firstBytes true), caller, [.trap]⟩ := by
  have discarded : Runs .call (.trapped (firstBytes true) [] []) :=
    trapDelivery.tail (.discard (.cut [] saved (seq.continuation [segment]) [] (Or.inl (by decide))))
  exact native ((discarded.tail .closeTrap).tail (.graph (.pure (.frameTrap 1 active))))

-- With an embedding that supplies no outcome, the same pending
-- configuration takes no successor at all.
example (choice : Bool) {dst : Config Nat} : ¬ Step CallFrame.v1NoHost (cfg (secondPending choice)) dst := by
  intro move
  have blocked : seq.Contract CallFrame.v1NoHost .fixed slot initial base :=
    fun _ _ _ _ _ _ _ _ outcome => outcome.elim
  obtain ⟨phase, transition, _, _⟩ :=
    (Sequence.v1_step_iff rfl checked layout trivial rfl blocked (readyOnRun (secondRun choice))).mp move
  cases transition with
  | returned outcome _ => exact outcome
  | diverged outcome => exact outcome

-- Static checking uses the first declared result type to admit the second
-- site, even if the embedding never returns normally at the first one.
example : Sequence.check fn (Prefix.stackTypes fn.initial)
    [seq.first, { segment with site := { second with signature := ⟨[.int .i64], [.int .i32]⟩ } }] = false := rfl

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.HostEntry.SequenceExamples
