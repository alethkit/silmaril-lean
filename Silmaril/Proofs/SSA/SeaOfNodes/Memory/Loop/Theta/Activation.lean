module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Theta.Defs
import Silmaril.SSA.SeaOfNodes.Memory.RVSDG.Thms
import Silmaril.SSA.RVSDG.Institution.Thms
import Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.ThetaProofs

open RVSDG (Locals Origin Port Tuple Wires)
open RVSDG.NestedTheta (identityPorts)
open RVSDG.OrderedRuntime.Structured
  (Opcode Threaded newestIndex newestPort readOrigin read_cons runtime)

variable {args : List ValueSort} {cells : Nat}

private theorem map_map {T : Type} {F G H : T → Type} {ports : List T}
    (xs : Tuple F ports) (f : ∀ t, F t → G t) (g : ∀ t, G t → H t) :
    (xs.map f).map g = xs.map (fun t x => g t (f t x)) := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp only [Tuple.map, ih]

private theorem get_identity {T : Type} {F : T → Type} {ports : List T} (xs : Tuple F ports) :
    (identityPorts ports).map (fun _ p => xs.get p) = xs := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp only [identityPorts, Tuple.map, map_map, Tuple.get, ih]

theorem read_args {entry : List (RVSDG.OrderedRuntime.Structured.Ty ValueSort)} (xs : Tuple (WireVal cells) entry) :
    Wires.read (SeaOfNodes.Loop.argWires entry []) xs PUnit.unit = xs := by
  unfold SeaOfNodes.Loop.argWires Wires.read
  rw [map_map]
  exact get_identity xs

private theorem get_newest {entry ports : List (RVSDG.OrderedRuntime.Structured.Ty ValueSort)} {t : RVSDG.OrderedRuntime.Structured.Ty ValueSort}
    {past : List (List (RVSDG.OrderedRuntime.Structured.Ty ValueSort))} (p : Port ports t)
    (xs : Tuple (WireVal cells) entry) (locals : Locals (WireVal cells) past)
    (out : Tuple (WireVal cells) ports) :
    readOrigin (.output (newestIndex ports past) (newestPort p past)) xs (locals.snoc out) =
      out.get p := by
  induction past with
  | nil => rfl
  | cons _ _ ih => exact ih locals.2

private theorem read_newest {entry ports : List (RVSDG.OrderedRuntime.Structured.Ty ValueSort)}
    {past : List (List (RVSDG.OrderedRuntime.Structured.Ty ValueSort))} (xs : Tuple (WireVal cells) entry)
    (locals : Locals (WireVal cells) past) (out : Tuple (WireVal cells) ports) :
    (newestWires past).read xs (locals.snoc out) = out := by
  unfold newestWires Wires.read
  rw [map_map]
  change (identityPorts ports).map
    (fun _ p => readOrigin (.output (newestIndex ports past) (newestPort p past)) xs (locals.snoc out)) = _
  simp only [get_newest, get_identity]

private theorem get_read {entry ports : List (RVSDG.OrderedRuntime.Structured.Ty ValueSort)} {t : RVSDG.OrderedRuntime.Structured.Ty ValueSort}
    {past : List (List (RVSDG.OrderedRuntime.Structured.Ty ValueSort))} (p : Port ports t)
    (wires : Wires entry past ports) (xs : Tuple (WireVal cells) entry)
    (locals : Locals (WireVal cells) past) :
    (wires.read xs locals).get p = readOrigin (wires.get p) xs locals := by
  induction p with
  | head => cases wires with | cons source rest => rw [read_cons]; rfl
  | tail _ ih => cases wires with | cons source rest => rw [read_cons]; exact ih rest

private theorem read_inputsWithHeap {entry : List (RVSDG.OrderedRuntime.Structured.Ty ValueSort)} {past : List (List (RVSDG.OrderedRuntime.Structured.Ty ValueSort))}
    (xs : Tuple (WireVal cells) entry) (locals : Locals (WireVal cells) past)
    (input : Tuple (Val cells) args) (heap : Heap cells) (live : Origin entry past runtime)
    (wire : ∀ {t}, Port (carrier args) t → Origin entry past t)
    (agree : ∀ {t} (p : Port (carrier args) t), readOrigin (wire p) xs locals = (encodeInput heap input).get p) :
    (inputsWithHeap live args wire).read xs locals = encodeInput (readOrigin live xs locals) input := by
  induction input with
  | nil => exact read_cons live .nil xs locals
  | cons x rest ih =>
    simp only [inputsWithHeap, read_cons, encodeInput]
    exact congrArg₂ Tuple.cons (agree .head) (ih (fun p => wire (.tail p)) (fun p => agree (.tail p)))

private def testRun (stop : Port args .word) (input : Tuple (Val cells) args) (word : Word)
    (heap : Heap cells) : Tuple (WireVal cells) (Threaded (tagged args)) :=
  (thetaRuntime cells).run (.ordered (.value (inputData args)) (.control (inputData args))
    (.pure (.check stop))) (.cons word (encodeInput heap input))

private theorem eval_testAfter (stop : Port args .word) (input : Tuple (Val cells) args) (heap : Heap cells) :
    {past sigs : List (List (RVSDG.OrderedRuntime.Structured.Ty ValueSort))} →
    (term : RVSDG.Term ThetaOpcode (carrier args) past sigs (Threaded wordPorts)) →
    (locals : Locals (WireVal cells) past) →
    (testAfter stop term).eval (thetaRuntime cells) (encodeInput heap input) locals =
      let out := term.eval (thetaRuntime cells) (encodeInput heap input) locals
      testRun stop input (out.get .head) (out.get (.tail .head))
  | _, _, .ret wires, locals => by
    let entry := encodeInput heap input
    let live := wires.get (.tail .head)
    let word := wires.get .head
    have routed := read_inputsWithHeap entry locals input heap live (fun p => .arg p) (fun _ => rfl)
    have observed : Wires.read (.cons word (inputsWithHeap live args (fun p => .arg p))) entry locals =
        .cons ((wires.read entry locals).get .head)
          (encodeInput ((wires.read entry locals).get (.tail .head)) input) :=
      (read_cons word _ entry locals).trans (congrArg₂ Tuple.cons
        (get_read .head wires entry locals).symm
        (routed.trans (congrArg (fun h => encodeInput h input)
          (get_read (.tail .head) wires entry locals).symm)))
    exact (read_newest entry locals _).trans (congrArg (fun xs => (thetaRuntime cells).run
      (.ordered (.value (inputData args)) (.control (inputData args)) (.pure (.check stop))) xs) observed)
  | _, _, .bind _ _ rest, _ => eval_testAfter stop input heap rest _

private theorem test_run (stop : Port args .word) (input : Tuple (Val cells) args)
    (word : Word) (heap : Heap cells) :
    testRun stop input word heap = .cons (continueTag word (input.get stop)) (encodeInput heap input) :=
  congrArg (fun w => Tuple.cons (t := .control 2) (continueTag word w) (encodeInput heap input))
    (encodeInput_get stop input heap)

private abbrev MemoryRun (cells : Nat) :=
  ∀ {ins outs}, Opcode NoPure Effect ins outs → Tuple (WireVal cells) ins → Tuple (WireVal cells) outs

private theorem reduct_run (cells : Nat) :
    @Eq (MemoryRun cells)
      (fun {_ _} op input => (RVSDG.Institution.reduct liftMemory (thetaRuntime cells)).run op input)
      (fun {_ _} op input => (Memory.leafModel cells).toRVSDG.run op input) := by
  funext ins outs op input
  cases op with
  | ordered _ _ instr =>
    cases instr with
    | pure op => exact nomatch op
    | effect effect => cases effect <;> cases input <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem body_run (graph : Graph args) (input : Tuple (Val cells) args) (heap : Heap cells) :
    graph.thetaBody.run (thetaRuntime cells) (encodeInput heap input) =
      let out := graph.body.denote input heap
      .cons (continueTag out.1 (graph.stopWord input)) (encodeInput out.2 input) := by
  have lowered : (RVSDG.Institution.mapTerm liftMemory graph.body.lowered.term).run
      (thetaRuntime cells) (encodeInput heap input) = let out := graph.body.denote input heap
      encodeResult out.1 out.2 := by
    let entry := encodeInput heap input
    let m := thetaRuntime cells
    calc
      _ = (RVSDG.Institution.mapTerm liftMemory graph.body.lowered.term).toGraph.run m entry :=
        (RVSDG.Term.run_toGraph _ m entry).symm
      _ = (RVSDG.Institution.mapGraph liftMemory graph.body.lower).run m entry :=
        congrArg (fun g => g.run m entry) (RVSDG.Institution.mapGraph_toGraph liftMemory graph.body.lowered.term).symm
      _ = graph.body.lower.run (RVSDG.Institution.reduct liftMemory m) entry :=
        RVSDG.Institution.mapGraph_run liftMemory m graph.body.lower entry
      _ = _ := by
        let evaluate := fun (run : MemoryRun cells) =>
          graph.body.lower.run (RVSDG.Model.mk (Val cells) (fun _ => Heap cells) run) entry
        have evaluated : graph.body.lower.run (RVSDG.Institution.reduct liftMemory m) entry =
            graph.body.lower.run (Memory.leafModel cells).toRVSDG entry :=
          @congrArg (MemoryRun cells) (Tuple (WireVal cells) (Threaded wordPorts))
            _ _ evaluate (reduct_run cells)
        exact evaluated.trans (graph.body.lower_run input heap)
  calc
    _ = (let out := (RVSDG.Institution.mapTerm liftMemory graph.body.lowered.term).run
          (thetaRuntime cells) (encodeInput heap input)
        testRun graph.stop input (out.get .head) (out.get (.tail .head))) :=
      eval_testAfter graph.stop input heap (past := []) _ PUnit.unit
    _ = _ :=
      (congrArg (fun out : Tuple (WireVal cells) (Threaded wordPorts) =>
        testRun graph.stop input (out.get .head) (out.get (.tail .head))) lowered).trans
        (test_run graph.stop input _ _)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.ThetaProofs
