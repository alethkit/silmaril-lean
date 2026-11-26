module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Thms
import Silmaril.Semantics.Elgot.Thms

/-! A typed classifier exposes the countdown's sum without changing the φ swap. -/

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Examples

open Silmaril.SSA.LambdaRTL
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics (Env)
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

private def input : Nat → Value Nat
  | 0 => .atom 2
  | 1 => .atom 5
  | 2 => .atom 1
  | _ => .atom 0

private def captured : Env Nat := input
private def ambient : Env Nat := fun _ => .unit

private def prim : Primitive → Value Nat → Part (Value Nat)
  | .classify, .atom 0 => Part.some (.inl (.atom 0))
  | .classify, .atom (n + 1) => Part.some (.inr (.atom n))
  | .readCaptures, .unit => Part.some (NamedFlat.Capture.packEnv 4 captured)
  | _, _ => Part.none

private theorem inputs (i : Fin 4) :
    captured i.val = CFG.Cyclic.Phi.inputEnv (NamedFlat.model prim) input (namedCaptures i, 0) := rfl

private def readCaptures : Tm Empty Primitive 0 := .op .readCaptures .unit

private def closed := (NamedFlat.Capture.close captureTypes blockTypes exitTypes
  admitted.val admitted.property.2 readCaptures
  (show HasType Primitive .nil .nil readCaptures captureType from .op .unit)).get (by decide)

private theorem packet (v : Value Nat) (state : Unit) :
    LambdaSSA.Semantics.Tm.Eval (NamedFlat.instr prim) ambient
      (Morphism.CaseSSA.erase readCaptures) () v state ↔
      v = NamedFlat.Capture.packEnv 4 captured ∧ state = () := by
  cases state
  constructor
  · intro run
    cases run with
    | op arg result =>
      cases arg
      exact ⟨Part.mem_some_iff.mp result, rfl⟩
  · rintro ⟨rfl, _⟩
    exact .op .unit (Part.mem_some _)

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
    Part.map_some, afterCountdown, upd, input]

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
  NamedFlat.Phi.packed_run_iff lowered admitted.property.1 inputs closed.property.1 closed.property.2 packet

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
  (NamedFlat.mutable_packed_run_iff admitted.property.1 inputs closed.property.1
    closed.property.2 packet).mpr (packed_iff.mp (Part.eq_some_iff.mp source_run))

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Examples
