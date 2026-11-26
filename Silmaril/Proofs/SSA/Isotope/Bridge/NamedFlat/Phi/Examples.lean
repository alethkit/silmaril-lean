module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Thms
import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Infinite.Thms
import Silmaril.Semantics.Elgot.Thms

/-! A typed classifier exposes the countdown's sum without changing the φ swap. -/

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Examples

open Silmaril.SSA.LambdaRTL
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics (Diverges Env)
open LambdaSSA.Semantics.Region (Eval)
open LetCase.LocallyNameless (Tm HasType)

private inductive Primitive
  | classify
  | readCaptures

private def num : Ty Unit := .base ()
private def captureTypes : BoundCtx (Ty Unit) 4 := .snoc (.snoc (.snoc (.snoc .nil num) num) num) num
private def captureType : Ty Unit := Region.packedInputType captureTypes.toList

private instance : HasTy Primitive (Ty Unit) where
  src
    | .classify => num
    | .readCaptures => .unit
  trg
    | .classify => .coprod num num
    | .readCaptures => captureType

open CFG.Cyclic.Phi (Graph br ret)

-- The latch saves the old left value and the header swaps the φ operands.
-- The countdown and saved register pass between blocks as ordinary live-ins.
private def header : CFG.Cyclic.Phi.Block Nat Nat Primitive :=
  ⟨[⟨0, [(none, .var 0), (some 20, .var 1)]⟩, ⟨1, [(none, .var 1), (some 20, .var 0)]⟩],
    .term (.case (.app .classify (.var 2)) 2
      (ret (.pair (.var 0) (.pair (.var 1) (.var 3)))) 2 (br 20))⟩

private def graph : Graph Nat Nat Primitive :=
  ⟨.term (br 10), [(10, header), (20, ⟨[], .let1 3 (.val (.var 0)) (.term (br 10))⟩)]⟩

private def mutable := CFG.Cyclic.Phi.lower graph
private def lexical := CFG.Cyclic.Versioning.compile mutable
private def namedCaptures (i : Fin 4) : Option Nat := some i.val
private def exitLabels : List (Option Nat) := [none]

private def blockTypes (i : Fin lexical.blocks.length) : Ty Unit :=
  let phiType := if i.val = 0 then Ty.product num (.product num .unit) else .unit
  .product phiType (.product num (.product num (.product num (.product num .unit))))

private def exitTypes (_ : Fin 1) : Ty Unit := .product num (.product num num)

private def admitted := (NamedFlat.compileTyped mutable exitLabels namedCaptures captureTypes
  blockTypes exitTypes).get (by decide)

private theorem lowered : CFG.Cyclic.Phi.compile graph = some lexical := by
  simp [CFG.Cyclic.Phi.compile, show graph.check = true by decide, lexical, mutable]

private def registers (left right saved : Nat) : Nat → Value Nat
  | 0 => .atom left
  | 1 => .atom right
  | 2 => .atom 1
  | 3 => .atom saved
  | _ => .atom 0

private def input := registers 2 5 0

private def captured : Env Nat := input
private def ambient : Env Nat := fun _ => .unit

private def prim : Primitive → Value Nat → Part (Value Nat)
  | .classify, .atom 0 => Part.some (.inl (.atom 0))
  | .classify, .atom (n + 1) => Part.some (.inr (.atom n))
  | .readCaptures, .unit => Part.some (NamedFlat.Capture.packEnv 4 captured)
  | _, _ => Part.none

private theorem inputs {operation : Primitive → Value Nat → Part (Value Nat)} (i : Fin 4) :
    captured i.val = CFG.Cyclic.Phi.inputEnv (NamedFlat.model operation) input (namedCaptures i, 0) := rfl

private def readCaptures : Tm Empty Primitive 0 := .op .readCaptures .unit

private def closed := (NamedFlat.Capture.close captureTypes blockTypes exitTypes
  admitted.val admitted.property.2 readCaptures
  (show HasType Primitive .nil .nil readCaptures captureType from .op .unit)).get (by decide)

private theorem packet {operation : Primitive → Value Nat → Part (Value Nat)}
    (read : operation .readCaptures .unit = Part.some (NamedFlat.Capture.packEnv 4 captured))
    (v : Value Nat) (state : Unit) :
    LambdaSSA.Semantics.Tm.Eval (NamedFlat.instr operation) ambient
      (Morphism.CaseSSA.erase readCaptures) () v state ↔
      v = NamedFlat.Capture.packEnv 4 captured ∧ state = () := by
  cases state
  constructor
  · intro run
    cases run with
    | op arg result =>
      cases arg
      change v ∈ operation .readCaptures .unit at result
      rw [read] at result
      exact ⟨Part.mem_some_iff.mp result, rfl⟩
  · rintro ⟨rfl, _⟩
    apply LambdaSSA.Semantics.Tm.Eval.op .unit
    change _ ∈ operation .readCaptures .unit
    rw [read]
    exact Part.mem_some _

private def model := NamedFlat.model prim
private def sourceStep := CFG.Cyclic.Phi.step model graph

private def result : Value Nat := .pair (.atom 5) (.pair (.atom 2) (.atom 2))

private def afterCountdown := upd (upd (upd input 0 (.atom 2)) 1 (.atom 5)) 2 (.atom 0)
private def afterLatch := upd afterCountdown 3 (.atom 2)
private def afterSwap := upd (upd (upd afterLatch 0 (.atom 5)) 1 (.atom 2)) 2 (.atom 0)

private theorem toLatch : sourceStep (.jump none 10, input) =
    Part.some (.inr (.jump (some 10) 20, afterCountdown)) := by
  simp [sourceStep, CFG.Cyclic.Phi.step, CFG.Cyclic.Phi.execute, CFG.Cyclic.Phi.assign,
    CFG.Cyclic.Phi.Row.operand, graph, header, CFG.Body.exec, CFG.Term.exec, Op.eval, Val.eval,
    model, NamedFlat.model, prim, br, Part.bind_eq_bind, Part.bind_some, Part.map_eq_map,
    Part.map_some, afterCountdown, upd, input, registers]

private theorem toHeader : sourceStep (.jump (some 10) 20, afterCountdown) =
    Part.some (.inr (.jump (some 20) 10, afterLatch)) := by
  simp [sourceStep, CFG.Cyclic.Phi.step, CFG.Cyclic.Phi.execute, CFG.Cyclic.Phi.assign,
    graph, List.lookup, CFG.Body.exec, CFG.Term.exec, Op.eval, Val.eval, afterCountdown,
    upd, model, NamedFlat.model, br, Part.bind_eq_bind, Part.bind_some, Part.map_eq_map,
    Part.map_some, afterLatch]

private theorem swapped : sourceStep (.jump (some 20) 10, afterLatch) =
    Part.some (.inr (.returned result, afterSwap)) := by
  simp [sourceStep, CFG.Cyclic.Phi.step, CFG.Cyclic.Phi.execute, CFG.Cyclic.Phi.assign,
    CFG.Cyclic.Phi.Row.operand, graph, header, List.lookup, CFG.Body.exec, CFG.Term.exec, Op.eval,
    Val.eval, model, NamedFlat.model, prim, ret, Part.bind_eq_bind, Part.bind_some, Part.map_eq_map,
    Part.map_some, afterLatch, afterCountdown, afterSwap, upd, result]

private theorem source_run : CFG.Cyclic.Phi.run model graph input = Part.some (none, result) := by
  have entered : CFG.Cyclic.Phi.execute model none graph.entry input =
      Part.some (.jump none 10, input) := rfl
  rw [CFG.Cyclic.Phi.run, entered, Part.bind_eq_bind, Part.bind_some]
  apply Part.eq_some_iff.mpr
  apply (Elgot.Part.mem_iter_iff sourceStep _ _).mpr
  exact .more (Part.eq_some_iff.mp toLatch) <|
    .more (Part.eq_some_iff.mp toHeader) <|
    .more (Part.eq_some_iff.mp swapped) <|
    .done (Part.mem_some _)

private theorem packed_iff {value : Value Nat} :
    (none, value) ∈ CFG.Cyclic.Phi.run model graph input ↔
      Eval (NamedFlat.instr prim) ambient (FiniteCFG.packedExecutionRegion closed.property.1)
        () 0 (.inl value) () :=
  NamedFlat.Phi.packed_run_iff lowered admitted.property.1 inputs closed.property.1 closed.property.2 (packet rfl)

-- The packed evaluator accepts the swapped pair and rejects the sequential result.
example : Eval (NamedFlat.instr prim) ambient (FiniteCFG.packedExecutionRegion closed.property.1)
    () 0 (.inl result) () :=
  packed_iff.mp (Part.eq_some_iff.mp source_run)

example : ¬ Eval (NamedFlat.instr prim) ambient (FiniteCFG.packedExecutionRegion closed.property.1)
    () 0 (.inl (.pair (.atom 5) (.pair (.atom 5) (.atom 2)))) () := by
  intro evaluated
  have returned := packed_iff.mpr evaluated
  rw [source_run, Part.mem_some_iff] at returned
  cases returned

-- The mutable bridge applies at the intermediate tuple-argument CFG.
example : (0, result) ∈ ((obs <$> CFG.Cyclic.run model mutable
    (CFG.Cyclic.Phi.liftStore .unit input)) >>= NamedFlat.numberExit exitLabels) :=
  (NamedFlat.mutable_packed_run_iff admitted.property.1 (inputs (operation := prim)) closed.property.1
    closed.property.2 (packet rfl)).mpr (packed_iff.mp (Part.eq_some_iff.mp source_run))

/-! ## One typed φ table with a repeating backedge and a stuck classifier -/

private def repeatingPrim : Primitive → Value Nat → Part (Value Nat)
  | .classify, .atom n => Part.some (.inr (.atom n))
  | op, value => prim op value

private def stuckPrim : Primitive → Value Nat → Part (Value Nat)
  | .classify, _ => Part.none
  | op, value => prim op value

private inductive LoopPosition
  | entry
  | header (left right saved : Nat)
  | latch (left right saved : Nat)

private def LoopPosition.pending : LoopPosition → CFG.Cyclic.Phi.Pending Nat Nat (Value Nat)
  | .entry => (.jump none 10, input)
  | .header left right saved => (.jump (some 20) 10, registers left right saved)
  | .latch left right saved => (.jump (some 10) 20, registers left right saved)

private def LoopPosition.next : LoopPosition → LoopPosition
  | .entry => .latch 2 5 0
  | .header left right saved => .latch right left saved
  | .latch left right _ => .header left right left

private theorem update_left (left right saved next : Nat) :
    upd (registers left right saved) 0 (.atom next) = registers next right saved := by
  funext reg
  rcases reg with _ | _ | _ | _ | reg <;> rfl

private theorem update_right (left right saved next : Nat) :
    upd (registers left right saved) 1 (.atom next) = registers left next saved := by
  funext reg
  rcases reg with _ | _ | _ | _ | reg <;> rfl

private theorem update_count (left right saved : Nat) :
    upd (registers left right saved) 2 (.atom 1) = registers left right saved := by
  funext reg
  rcases reg with _ | _ | _ | _ | reg <;> rfl

private theorem update_saved (left right saved next : Nat) :
    upd (registers left right saved) 3 (.atom next) = registers left right next := by
  funext reg
  rcases reg with _ | _ | _ | _ | reg <;> rfl

private theorem loop_step (pos : LoopPosition) :
    CFG.Cyclic.Phi.step (NamedFlat.model repeatingPrim) graph pos.pending =
      Part.some (.inr pos.next.pending) := by
  cases pos <;>
    simp [LoopPosition.pending, LoopPosition.next, CFG.Cyclic.Phi.step, CFG.Cyclic.Phi.execute,
      CFG.Cyclic.Phi.assign, CFG.Cyclic.Phi.Row.operand, graph, header, List.lookup, CFG.Body.exec,
      CFG.Term.exec, Op.eval, Val.eval, NamedFlat.model, repeatingPrim, br,
      Part.bind_eq_bind, Part.bind_some, Part.map_eq_map, Part.map_some,
      input, registers, update_left, update_right, update_count, update_saved]

private theorem repeats : CFG.Cyclic.Phi.InfiniteRun (NamedFlat.model repeatingPrim) graph input := by
  let position : Nat → LoopPosition := Nat.rec .entry (fun _ pos => pos.next)
  refine ⟨fun i => (position i).pending, Part.mem_some _, fun i => ?_⟩
  exact Part.eq_some_iff.mp (loop_step (position i))

private theorem stuck_step :
    CFG.Cyclic.Phi.step (NamedFlat.model stuckPrim) graph LoopPosition.entry.pending = Part.none := by
  simp [LoopPosition.pending, CFG.Cyclic.Phi.step, CFG.Cyclic.Phi.execute, CFG.Cyclic.Phi.assign,
    CFG.Cyclic.Phi.Row.operand, graph, header, CFG.Body.exec, CFG.Term.exec, Op.eval, Val.eval,
    NamedFlat.model, stuckPrim, Part.bind_eq_bind, Part.bind_none, Part.map_eq_map, Part.map_none]

private theorem stuck_has_no_path : ¬ CFG.Cyclic.Phi.InfiniteRun (NamedFlat.model stuckPrim) graph input := by
  rintro ⟨path, entered, steps⟩
  have initial : path 0 = LoopPosition.entry.pending := Part.mem_some_iff.mp entered
  have first := steps 0
  rw [initial, stuck_step] at first
  exact Part.notMem_none _ first

example : CFG.Cyclic.Phi.run (NamedFlat.model repeatingPrim) graph input = Part.none :=
  NamedFlat.Phi.run_eq_none_of_infinite lowered repeats

example : CFG.Cyclic.Phi.run (NamedFlat.model stuckPrim) graph input = Part.none := by
  have entry : CFG.Cyclic.Phi.execute (NamedFlat.model stuckPrim) none graph.entry input =
      Part.some LoopPosition.entry.pending := rfl
  rw [CFG.Cyclic.Phi.run, entry, Part.bind_eq_bind, Part.bind_some,
    Elgot.Part.fixpoint (CFG.Cyclic.Phi.step (NamedFlat.model stuckPrim) graph)]
  dsimp only
  rw [stuck_step, Part.bind_eq_bind, Part.bind_none]

example : Diverges (NamedFlat.instr repeatingPrim)
    (.region ambient (FiniteCFG.packedExecutionRegion closed.property.1) ()) :=
  (NamedFlat.Phi.packed_infinite_run_iff lowered admitted.property.1 inputs
    closed.property.1 closed.property.2 (packet rfl)).mp repeats

example : ¬ Diverges (NamedFlat.instr stuckPrim)
    (.region ambient (FiniteCFG.packedExecutionRegion closed.property.1) ()) :=
  fun div => stuck_has_no_path
    ((NamedFlat.Phi.packed_infinite_run_iff lowered admitted.property.1 inputs
      closed.property.1 closed.property.2 (packet rfl)).mpr div)

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Examples
