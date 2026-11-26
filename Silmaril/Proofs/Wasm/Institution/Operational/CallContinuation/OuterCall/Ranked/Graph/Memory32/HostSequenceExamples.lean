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


namespace EnclosingTail

private def savedPrefix : List Value := [Value.int .i64 42]
private def nextType : Wasm.V1.FuncType := ⟨[.int .i64, .int .i32], [.int .i32]⟩
private def nextSite : HostCall.V1.Site Nat := { second with signature := nextType }
private def entryFn : Function := { fn with initial := savedPrefix, code := [] }
private def entry : Sequence Nat := ⟨⟨⟨0⟩, rootAddr, entryFn, [.get ⟨0⟩], first⟩, []⟩
private def scalar : Option NumType := some (.int .i32)
private def tailRegion : Source Nat := .hosts ⟨[], nextSite⟩ []
private def arm : Source Nat := .ifThen scalar ⟨0⟩ .root (.hosts ⟨[.get ⟨0⟩], first⟩ []) (.plain [])
private def body : Source Nat := .blockThen scalar arm tailRegion
private def allocation : Store Nat :=
  { funcs := [.host hostType 11, .host nextType 19, .wasm entryFn.declaration.type mod (entry.v1FuncFor body)],
    memories := [initial] }
private def stored (bytes : ByteArray) := storeWithBytes allocation slot initial bytes
private def innerLabel : OpenLabel Nat := ⟨[], scalar, .plain []⟩
private def outerLabel : OpenLabel Nat := ⟨savedPrefix, scalar, tailRegion⟩
private def labels := [innerLabel, outerLabel]

private def behavior : HostSemantics Nat := fun id store operands answer =>
  (id = first.target ∧ store = stored initial.data ∧ operands = rootArgs ∧
    ((∃ choice : Bool, answer = .returned (stored (firstBytes choice)) (.values [firstValue choice])) ∨
      answer = .returned (stored (firstBytes true)) .trap)) ∨
  ∃ choice : Bool, id = nextSite.target ∧ store = stored (firstBytes choice) ∧
    operands = savedPrefix ++ [firstValue choice] ∧
    (answer = .returned store (.values [i32 (word choice)]) ∨ answer = .diverged)

private theorem siteOf {site : HostCall.V1.Site Nat} (used : site ∈ entry.sourceSites body) :
    site = first ∨ site = nextSite := by
  change site ∈ [first, first, nextSite] at used
  simpa using used

private theorem admitted : entry.Checked .fixed graph slot .ranked allocation caller rootArgs body where
  resolved := rfl
  allocated := rfl
  parameters := rfl
  scalar := by decide
  slot := rfl
  linkedHosts := by
    intro site used
    rcases siteOf used with rfl | rfl <;> exact ⟨rfl, rfl, by decide⟩
  typedBody := rfl
  guardedBody := by
    refine ⟨trivial, ?_, trivial, trivial⟩
    intro _ member
    cases member
  supportedTail := rfl
  linkedTail := by intro _ used; cases used

private theorem storeLayout : Layout graph allocation slot initial where
  memory := rfl
  functions := by intro _ _ found; simp [graph, Program.lookup] at found

private theorem embedding : entry.Contract behavior .fixed slot initial allocation body := by
  intro site used bytes _ operands _ after result outcome
  have signature : site.signature.results = [.int .i32] := by rcases siteOf used with rfl | rfl <;> rfl
  rcases outcome with ⟨_, store, _, ⟨choice, equal⟩ | trap⟩ | ⟨choice, _, store, _, equal | impossible⟩
  · cases equal
    rw [store, signature]
    cases choice
    · exact ⟨rfl, initial.data, firstBytes false, rfl, rfl, rfl⟩
    · exact ⟨rfl, initial.data, firstBytes true, rfl, rfl, rfl⟩
  · cases trap
    rw [store]
    exact ⟨trivial, initial.data, firstBytes true, rfl, rfl, rfl⟩
  · cases equal
    rw [store, signature]
    cases choice
    · exact ⟨rfl, firstBytes false, firstBytes false, rfl, rfl, rfl⟩
    · exact ⟨rfl, firstBytes true, firstBytes true, rfl, rfl, rfl⟩
  · cases impossible

private abbrev TailRuns := entry.Runs behavior .fixed graph slot allocation initial initial.data caller rootArgs
private abbrev renderPhase := entry.render allocation slot initial initial.data caller rootArgs
private def launch : Config Nat := ⟨stored initial.data, caller, values rootArgs ++ [.source (.call ⟨0⟩)]⟩
private def inside := entryFn.declaration.frame rootArgs

private theorem tailReady {phase : Phase} (run : TailRuns (.call body) phase) :
    entry.Ready .fixed graph slot .ranked initial phase body := by
  induction run with
  | refl => rfl
  | tail _ move ih => exact move.ready rfl admitted storeLayout rfl embedding ih

private theorem nativeTail {phase : Phase} (run : TailRuns (.call body) phase) :
    Steps behavior launch (renderPhase phase) :=
  (Sequence.v1_call_run_iff rfl admitted storeLayout trivial rfl embedding).mpr ⟨phase, run, tailReady run, rfl⟩

private theorem entersArm :
    TailRuns (.call body) (.pending initial.data [] rootArgs first [] labels) := by
  have opens : TailRuns (.call body) (.if_ initial.data [] scalar ⟨0⟩ .root
      (.hosts ⟨[.get ⟨0⟩], first⟩ []) (.plain []) [outerLabel]) :=
    ((Relation.ReflTransGen.single .resolve).tail .enter).tail .openBlock
  have selects : TailRuns (.call body) (.block initial.data [] scalar .root (.plain []) [outerLabel]) :=
    (opens.tail (.readCondition rfl)).tail .select
  exact ((selects.tail .openBlock).tail (.numeric (.get rfl))).tail (.hostResolve rfl)

private def nextPending (choice : Bool) : Phase :=
  .pending (firstBytes choice) [] (savedPrefix ++ [firstValue choice]) nextSite []

private theorem reachesTail (choice : Bool) : TailRuns (.call body) (nextPending choice) := by
  have returned : behavior first.target (stored initial.data) rootArgs
      (.returned (stored (firstBytes choice)) (.values [firstValue choice])) :=
    .inl ⟨rfl, rfl, rfl, .inl ⟨choice, rfl⟩⟩
  have inner : TailRuns (.call body) (.completed (firstBytes choice) [firstValue choice] innerLabel [outerLabel]) :=
    entersArm.tail (.returned returned rfl)
  have outer : TailRuns (.call body) (.completed (firstBytes choice) [firstValue choice] outerLabel []) :=
    inner.tail (.closeLabel rfl)
  exact (outer.tail (.closeLabel rfl)).tail
    (.hostResolve (saved := []) (actual := savedPrefix ++ [firstValue choice]) (site := nextSite) rfl)

-- Both the mixed-width saved prefix and the arm result are consumed by
-- the distinct host in the enclosing continuation, using the returned bytes.
example (choice : Bool) : Steps behavior launch
    ⟨stored (firstBytes choice), caller, [.frame 1 inside
      [.label 1 [] (values (savedPrefix ++ [firstValue choice]) ++ [.invoke nextSite.address])]]⟩ :=
  nativeTail (reachesTail choice)

example (choice : Bool) : Steps behavior launch ⟨stored (firstBytes choice), caller, values [i32 (word choice)]⟩ := by
  have returned : behavior nextSite.target (stored (firstBytes choice)) (savedPrefix ++ [firstValue choice])
      (.returned (stored (firstBytes choice)) (.values [i32 (word choice)])) :=
    .inr ⟨choice, rfl, rfl, rfl, .inl rfl⟩
  have deliver := (reachesTail choice).tail (.returned returned rfl)
  exact nativeTail ((deliver.tail (.graph (.frame (.pure (.labelDone 1 [] [i32 (word choice)])) 1 caller)))
    |>.tail (.graph (.pure (.frameDone 1 inside [i32 (word choice)] rfl))))

-- Divergence at the resumed host still steps to the same pending call.
example (choice : Bool) : Step behavior (renderPhase (nextPending choice)) (renderPhase (nextPending choice)) := by
  exact .frame (.label (.invokeHostDiverges _ _ nextSite.address nextType nextSite.target
    (savedPrefix ++ [firstValue choice]) rfl rfl (.inr ⟨choice, rfl, rfl, rfl, .inr rfl⟩)) 1 []) 1 caller

-- In an embedding with no outcome, this pending invocation has no native step.
example (choice : Bool) {dst : Config Nat} : ¬ Step CallFrame.v1NoHost (renderPhase (nextPending choice)) dst := by
  intro move
  have blocked : entry.Contract CallFrame.v1NoHost .fixed slot initial allocation body :=
    fun _ _ _ _ _ _ _ _ outcome => outcome.elim
  obtain ⟨_, transition, _, _⟩ :=
    (Sequence.v1_step_iff rfl admitted storeLayout trivial rfl blocked (tailReady (reachesTail choice))).mp move
  cases transition with
  | returned outcome _ => exact outcome
  | diverged outcome => exact outcome

private def trapped : Phase := .trapped (firstBytes true) [] [] labels

private theorem armTrap : TailRuns (.call body) trapped := by
  have returned : behavior first.target (stored initial.data) rootArgs (.returned (stored (firstBytes true)) .trap) :=
    .inl ⟨rfl, rfl, rfl, .inr rfl⟩
  exact entersArm.tail (.returned returned rfl)

-- The inner label closes, then the outer label closes. This exposes the
-- saved prefix and the pending host instruction to trap cleanup.
example : Steps behavior launch
    ⟨stored (firstBytes true), caller, [.frame 1 inside
      [.label 1 [] (values savedPrefix ++ [.trap, .source (.call nextSite.index)])]]⟩ :=
  nativeTail ((armTrap.tail .closeTrap).tail .closeTrap)

example : Steps behavior launch ⟨stored (firstBytes true), caller, [.trap]⟩ := by
  have discarded : TailRuns (.call body) (.trapped (firstBytes true) [] []) :=
    ((armTrap.tail .closeTrap).tail .closeTrap).tail
      (.discard (.cut [] savedPrefix ([.source (.call nextSite.index)] : List Admin) [] (Or.inl (by decide))))
  exact nativeTail ((discarded.tail .closeTrap).tail (.graph (.pure (.frameTrap 1 inside))))

example (run : TailRuns trapped (nextPending true)) : False := by
  rcases Sequence.trapped_run run with ⟨_, _, _, impossible⟩ | ⟨_, impossible⟩ <;> cases impossible

-- A mismatched enclosing host signature is rejected before arm selection.
example : entry.checkSource (Prefix.stackTypes savedPrefix) entryFn.declaration.results entryFn.entryLabels
    (.blockThen scalar arm (.hosts ⟨[], { nextSite with signature := hostType }⟩ [])) = false := rfl

-- A host-free suffix that would lose the typed reentry stack is also rejected.
example : entry.checkSource (Prefix.stackTypes savedPrefix) entryFn.declaration.results entryFn.entryLabels
    (.blockThen scalar (.plain [.ranked (.numeric (.get ⟨0⟩))]) tailRegion) = false := rfl

end EnclosingTail
end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.HostEntry.SequenceExamples
