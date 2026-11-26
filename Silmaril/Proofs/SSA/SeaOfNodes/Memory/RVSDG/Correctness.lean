module

public import Silmaril.SSA.SeaOfNodes.Memory.RVSDG.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Thms
import Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.RVSDGProofs

open RVSDG (Locals Origin Port Tuple Wires)
open RVSDG.OrderedRuntime.Structured
  (Threaded Ty nextRuntime newestIndex newestPort primitiveNode readOrigin
    read_appended read_cons runtime runtimePort withRuntime)
open RVSDG.NestedTheta.ExplicitRuntime.Splice (olderIndex olderPort weaken)

variable {args : List ValueSort} {past : List (List ValueSort)} {version cells : Nat}
variable {target : List (List (Ty ValueSort))}

theorem load_run (address : Address cells) (heap : Heap cells) :
    (leafModel cells).toRVSDG.run (.ordered (.value .nil) wordData (.effect .load))
      (withRuntime heap (.cons address .nil)) = encodeResult (heap.read address) heap :=
  rfl

private theorem read_older {head : List (Ty ValueSort)} {t : Ty ValueSort} (x : Tuple (WireVal cells) head) :
    (scope : List (List (Ty ValueSort))) → (i : Fin scope.length) →
    (p : Port scope[i] t) → (locals : Locals (WireVal cells) scope) →
    ((locals.snoc x).get (olderIndex head scope i)).get (olderPort head scope i p) =
      (locals.get i).get p
  | [], i => i.elim0
  | h :: scope, i =>
    Fin.cases (motive := fun j => ∀ (p : Port (h :: scope)[j] t) (locals : Locals (WireVal cells) (h :: scope)),
      ((locals.snoc x).get (olderIndex head (h :: scope) j)).get (olderPort head (h :: scope) j p) =
        (locals.get j).get p)
      (fun _ _ => rfl) (fun j p locals => read_older x scope j p locals.2) i

private theorem read_weak {entryPorts head : List (Ty ValueSort)} {t : Ty ValueSort}
    (wire : Origin entryPorts target t) (entry : Tuple (WireVal cells) entryPorts)
    (locals : Locals (WireVal cells) target) (x : Tuple (WireVal cells) head) :
    readOrigin (weaken head wire) entry (locals.snoc x) = readOrigin wire entry locals := by
  cases wire with
  | arg => rfl
  | output i p => exact read_older x target i p locals

private theorem read_newest {head : List (Ty ValueSort)} {t : Ty ValueSort}
    (p : Port head t) (locals : Locals (WireVal cells) target) (x : Tuple (WireVal cells) head) :
    ((locals.snoc x).get (newestIndex head target)).get (newestPort p target) = x.get p := by
  induction target with
  | nil => rfl
  | cons _ _ ih => exact ih locals.2

private theorem read_next {data entry : List (Ty ValueSort)}
    (entryValues : Tuple (WireVal cells) entry) (locals : Locals (WireVal cells) target)
    (heap : Heap cells) (value : Tuple (WireVal cells) data) :
    readOrigin (nextRuntime target data) entryValues (locals.snoc (withRuntime heap value)) = heap :=
  (read_newest (runtimePort data) locals _).trans
    (RVSDG.OrderedRuntime.Structured.get_runtime heap value)

private abbrev Reads (routing : Routing args past target)
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past)
    (entry : Tuple (WireVal cells) (Threaded (dataPorts args))) (regs : Locals (WireVal cells) target) :=
  ∀ {sort} (wire : Origin args past sort),
    readOrigin (routing wire) entry regs = readValue wire input locals

private theorem read_argument {sort : ValueSort} (port : Port args sort)
    (input : Tuple (Val cells) args) (heap : Heap cells) :
    (encodeInput heap input).get (argumentPort port) = input.get port := by
  induction port with
  | head => cases input; rfl
  | tail p ih => cases input with | cons _ tail => exact ih tail

private theorem read_entry (input : Tuple (Val cells) args) (heap : Heap cells) :
    Reads (Routing.entry args) input PUnit.unit (encodeInput heap input) PUnit.unit := by
  intro sort wire
  cases wire with
  | arg p => exact read_argument p input heap
  | output i _ => exact i.elim0

private theorem read_start_heap (input : Tuple (Val cells) args) (heap : Heap cells) :
    (encodeInput heap input).get (runtimePort (dataPorts args)) = heap := by
  induction input with
  | nil => rfl
  | cons _ _ ih => exact ih

variable {routing : Routing args past target} {input : Tuple (Val cells) args}
variable {locals : Locals (Val cells) past}
variable {entry : Tuple (WireVal cells) (Threaded (dataPorts args))}
variable {regs : Locals (WireVal cells) target}

private theorem after_store (agree : Reads routing input locals entry regs) (heap : Heap cells) :
    Reads routing.afterStore input locals entry (regs.snoc (withRuntime heap .nil)) := by
  intro sort wire
  exact (read_weak (routing wire) entry regs _).trans (agree wire)

private theorem after_load (agree : Reads routing input locals entry regs)
    (value : Word) (heap : Heap cells) :
    Reads routing.afterLoad input (.cons value .nil, locals) entry (regs.snoc (encodeResult value heap)) := by
  intro sort wire
  cases wire with
  | arg p => exact (read_weak (routing (.arg p)) entry regs _).trans (agree (.arg p))
  | output i p =>
    refine Fin.cases (motive := fun j => ∀ q : Port ([.word] :: past)[j] sort,
      readOrigin (routing.afterLoad (.output j q)) entry (regs.snoc (encodeResult value heap)) =
        readValue (.output (past := [.word] :: past) j q) input (.cons (t := ValueSort.word) value .nil, locals)) ?_ ?_ i p
    · intro q
      cases q with
      | head => exact read_newest .head regs (encodeResult value heap)
      | tail p => exact nomatch p
    · intro j q
      exact (read_weak (routing (.output j q)) entry regs _).trans (agree (.output j q))

private theorem read_nil {ins : List (Ty ValueSort)} (entry : Tuple (WireVal cells) ins)
    (regs : Locals (WireVal cells) target) : Wires.read (.nil : Wires ins target []) entry regs = .nil :=
  rfl

private theorem lower_eval (body : Body args past version)
    (routing : Routing args past target) (live : Origin (Threaded (dataPorts args)) target runtime)
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past)
    (entry : Tuple (WireVal cells) (Threaded (dataPorts args))) (regs : Locals (WireVal cells) target)
    (agree : Reads routing input locals entry regs) :
    (body.lowerFrom routing live).term.eval (leafModel cells).toRVSDG entry regs =
      let result := body.denote input locals (readOrigin live entry regs)
      encodeResult result.1 result.2 := by
  induction body generalizing target with
  | ret memory value =>
    simp only [Body.lowerFrom, RVSDG.Term.eval, read_appended, read_cons, read_nil, agree, Body.denote, encodeResult]
  | load memory address rest ih =>
    simp only [Body.lowerFrom, RVSDG.Term.eval, primitiveNode, RVSDG.Shape.eval, read_appended,
      read_cons, read_nil, agree, Body.denote]
    let heap := readOrigin live entry regs
    let word := heap.read (readValue address input locals)
    have next := ih routing.afterLoad (nextRuntime target wordPorts) _ _ (after_load agree word heap)
    have state : readOrigin (nextRuntime target wordPorts) entry (regs.snoc (encodeResult word heap)) =
        heap := read_next (data := wordPorts) entry regs heap (.cons word .nil)
    rw [state] at next
    exact next
  | store memory address value rest ih =>
    simp only [Body.lowerFrom, RVSDG.Term.eval, primitiveNode, RVSDG.Shape.eval, read_appended,
      read_cons, read_nil, agree, Body.denote]
    let heap := (readOrigin live entry regs).write
      (readValue address input locals) (readValue value input locals)
    have next := ih routing.afterStore (nextRuntime target []) locals _ (after_store agree heap)
    have state : readOrigin (nextRuntime target []) entry (regs.snoc (withRuntime heap .nil)) = heap :=
      read_next entry regs heap .nil
    rw [state] at next
    exact next

theorem lower_run (graph : Graph args) (input : Tuple (Val cells) args) (heap : Heap cells) :
    graph.lower.run (leafModel cells).toRVSDG (encodeInput heap input) =
      let result := graph.denote input heap
      encodeResult result.1 result.2 := by
  rw [Graph.lower, RVSDG.Term.run_toGraph]
  have run := lower_eval graph (Routing.entry args) (.arg (runtimePort (dataPorts args))) input PUnit.unit
    (encodeInput heap input) PUnit.unit (read_entry input heap)
  simpa only [Graph.denote, Graph.lowered, RVSDG.Term.run, readOrigin, read_start_heap] using run

theorem lower_returns_iff (graph : Graph args) (input : Tuple (Val cells) args) (heap : Heap cells)
    (value : Word) (final : Heap cells) :
    graph.Returns input heap value final ↔
      graph.lower.run (leafModel cells).toRVSDG (encodeInput heap input) = encodeResult value final := by
  rw [graph.returns_iff_denote, lower_run]
  constructor
  · intro eq
    rw [eq]
  · intro eq
    exact Prod.ext
      (congrArg (fun xs : Tuple (WireVal cells) (Threaded wordPorts) => xs.get .head) eq)
      (congrArg (fun xs : Tuple (WireVal cells) (Threaded wordPorts) => xs.get (.tail .head)) eq)

end Silmaril.SSA.SeaOfNodes.Memory.RVSDGProofs
