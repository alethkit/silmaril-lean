module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.RVSDG.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.Memory.RVSDG.Thms
import Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.RVSDGProofs

open RVSDG (Locals Origin Port Tuple Wires)
open RVSDG.OrderedRuntime.Structured
  (Threaded Ty gammaNode nextRuntime read_cons readOrigin runtimePort withRuntime)
open SeaOfNodes.Diamond (Projection Slot)

variable {args : List ValueSort} {cells : Nat}

private theorem index_slot (slot : Slot) : indexSlot (slotIndex slot) = slot := by
  cases slot <;> rfl

private theorem read_argumentWires {entryPorts : List (Ty ValueSort)}
    {past : List (List (Ty ValueSort))} (entry : Tuple (WireVal cells) entryPorts)
    (locals : Locals (WireVal cells) past) (heap : Heap cells)
    (input : Tuple (Val cells) args)
    (wire : ∀ {t}, Port (Threaded (dataPorts args)) t → Origin entryPorts past t)
    (agree : ∀ {t} (p : Port (Threaded (dataPorts args)) t),
      readOrigin (wire p) entry locals = (encodeInput heap input).get p) :
    Wires.read (withRuntime (wire (runtimePort (dataPorts args))) (argumentWires args wire)) entry locals =
      encodeInput heap input := by
  induction input with
  | nil =>
    exact (read_cons (wire .head) .nil entry locals).trans
      (congrArg (fun rt => Tuple.cons rt .nil) (agree .head))
  | cons x xs ih =>
    simp only [argumentWires, withRuntime, read_cons, encodeInput]
    exact congrArg₂ Tuple.cons (agree .head) (ih (fun p => wire (.tail p)) (fun p => agree (.tail p)))

private theorem read_captures (graph : Graph args) (guard : Bool)
    (input : Tuple (Val cells) args) (heap : Heap cells) :
    Wires.read (withRuntime (.arg (runtimePort (inputPorts args))) (captures args))
      (graph.encodeEntry guard input heap) PUnit.unit = encodeInput heap input :=
  read_argumentWires _ _ heap input (fun p => .arg (.tail p)) (fun _ => rfl)

private theorem read_gamma (graph : Graph args) (guard : Bool)
    (input : Tuple (Val cells) args) (heap : Heap cells) :
    Wires.read (F := WireVal cells)
      (.cons (.arg .head) (withRuntime (.arg (runtimePort (inputPorts args))) (captures args)))
      (graph.encodeEntry guard input heap) PUnit.unit =
      .cons (t := .control 2) ⟨slotIndex (graph.merge.slot (Projection.ofBool guard))⟩
        (encodeInput heap input) :=
  (read_cons (past := []) (.arg .head) _ (graph.encodeEntry guard input heap) PUnit.unit).trans
    (congrArg (Tuple.cons _) (read_captures graph guard input heap))

private theorem run_suffix (graph : Graph args) (guard : Bool) (input : Tuple (Val cells) args)
    (heap : Heap cells) (boundary : Tuple (WireVal cells) (Threaded wordPorts)) :
    (graph.suffix.lowerAt (diamondData args) (suffixRouting args) (nextRuntime [] wordPorts)).term.eval
        (leafModel cells).toRVSDG (graph.encodeEntry guard input heap)
        (Locals.snoc (past := []) PUnit.unit boundary) =
      graph.suffix.lower.run (leafModel cells).toRVSDG
        (encodeInput (boundary.get (.tail .head)) (.cons (boundary.get .head) input)) := by
  let suffixInput := Tuple.cons (t := ValueSort.word) (boundary.get .head) input
  let suffixHeap := boundary.get (.tail .head)
  refine (graph.suffix.lowerAt_eval (diamondData args) (suffixRouting args) (nextRuntime [] wordPorts)
    suffixInput PUnit.unit (graph.encodeEntry guard input heap) (Locals.snoc (past := []) PUnit.unit boundary)
    ?_).trans (Memory.Graph.lower_run graph.suffix suffixInput suffixHeap).symm
  intro sort wire
  cases wire with
  | arg p =>
    cases p with
    | head => rfl
    | tail p => exact encodeInput_get p input heap
  | output i _ => exact i.elim0

theorem lower_run_selected (graph : Graph args) (guard : Bool)
    (input : Tuple (Val cells) args) (heap : Heap cells) :
    graph.lower.run (leafModel cells).toRVSDG (graph.encodeEntry guard input heap) =
      let selected := (graph.arm (Projection.ofBool guard)).lower.run
        (leafModel cells).toRVSDG (encodeInput heap input)
      graph.suffix.lower.run (leafModel cells).toRVSDG
        (encodeInput (selected.get (.tail .head)) (.cons (selected.get .head) input)) := by
  rw [Graph.lower, RVSDG.Term.run_toGraph]
  let child := fun (j : Fin 2) (entry : Tuple (WireVal cells) (Threaded (dataPorts args))) =>
    (graph.arm (graph.merge.predecessor (indexSlot j))).lowered.term.run (leafModel cells).toRVSDG entry
  let evaluate := (RVSDG.Shape.gamma (entry := Threaded (dataPorts args))
    (exit := Threaded wordPorts) 0).eval (leafModel cells).toRVSDG child
  let suffix := fun (boundary : Tuple (WireVal cells) (Threaded wordPorts)) =>
    (graph.suffix.lowerAt (diamondData args) (suffixRouting args) (nextRuntime [] wordPorts)).term.eval
      (leafModel cells).toRVSDG (graph.encodeEntry guard input heap) (Locals.snoc (past := []) PUnit.unit boundary)
  apply Eq.trans (congrArg (fun inputs => suffix (evaluate inputs)) (read_gamma graph guard input heap))
  change suffix (child (slotIndex (graph.merge.slot (Projection.ofBool guard))) (encodeInput heap input)) = _
  have edge : graph.merge.predecessor (indexSlot (slotIndex (graph.merge.slot (Projection.ofBool guard)))) =
      Projection.ofBool guard := by
    rw [index_slot, graph.merge.predecessor_slot]
  dsimp only [child]
  rw [edge]
  simpa only [Memory.Graph.lower, RVSDG.Term.run_toGraph] using run_suffix graph guard input heap _

theorem lower_run (graph : Graph args) (guard : Bool)
    (input : Tuple (Val cells) args) (heap : Heap cells) :
    graph.lower.run (leafModel cells).toRVSDG (graph.encodeEntry guard input heap) =
      let result := graph.denote guard input heap
      encodeResult result.1 result.2 := by
  rw [lower_run_selected]
  simp only [Memory.Graph.lower_run (graph.arm (Projection.ofBool guard)) input heap]
  exact Memory.Graph.lower_run graph.suffix _ _

theorem lower_returns_iff (graph : Graph args) (guard : Bool)
    (input : Tuple (Val cells) args) (heap : Heap cells) (value : Word) (final : Heap cells) :
    graph.Returns guard input heap value final ↔
      graph.lower.run (leafModel cells).toRVSDG (graph.encodeEntry guard input heap) =
        encodeResult value final := by
  rw [graph.returns_iff_denote, lower_run]
  constructor
  · intro eq
    rw [eq]
  · intro eq
    exact Prod.ext
      (congrArg (fun xs : Tuple (WireVal cells) (Threaded wordPorts) => xs.get .head) eq)
      (congrArg (fun xs : Tuple (WireVal cells) (Threaded wordPorts) => xs.get (.tail .head)) eq)

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.RVSDGProofs
