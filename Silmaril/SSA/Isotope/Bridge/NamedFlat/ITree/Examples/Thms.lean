module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Thms
import Silmaril.SSA.Isotope.Bridge.NamedFlat.Capture.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.FlatDispatcher.Execution.ITree.Thms

/-! # Typed requests at the captured entry and the back edge -/

namespace Silmaril.Isotope.Bridge.NamedFlat.Interaction.Examples

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG (Body Block Term)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region Primitive Transfer BlockInput splitTransfer)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues ModelTree Compatible)
open Silmaril.Elgot (iter)
open Silmaril.Elgot.ITree (Tree vis vis_bind iterate_fixpoint)
open LambdaSSA.FiniteCFG (packedExecutionRegion packedExecution_tree packedTreeOutput)

private abbrev SortName := ULift.{1} Unit
private abbrev Atom := ULift.{1} Nat
private abbrev Reg := ULift.{1} Unit
private abbrev Label := ULift.{1} Nat

private instance : AtomValues SortName := ⟨fun _ => Atom⟩

private abbrev Runtime := Sigma (AtomValues.carrier (κ := SortName))
private def atom (n : Nat) : Value Runtime := .atom ⟨⟨()⟩, ⟨n⟩⟩

private inductive Opcode
  | seed
  | tick
  | capture

private inductive Event : Type → Type
  | call (op : Opcode) (arg : Nat) : Event Nat
  | capture : Event Nat
  | malformed (op : Opcode) : Event Empty

private def num : Ty SortName := .base ⟨()⟩
private def captures : BoundCtx (Ty SortName) 1 := .snoc .nil num
private def edgeType : Ty SortName := .product num .unit
private def inputType : Ty SortName := LambdaSSA.Region.packedInputType captures.toList

private instance : HasTy Opcode (Ty SortName) where
  src
    | .capture => .unit
    | .seed | .tick => num
  trg
    | .capture => inputType
    | .seed | .tick => num

private def typed : Silmaril.Isotope.Semantics.InstructionModel
    (Ty.denote (AtomValues.carrier (κ := SortName))) Opcode (ModelTree Event) where
  eval
    | .seed, arg => vis (.call .seed arg.down) fun reply => pure (ULift.up reply)
    | .tick, arg => vis (.call .tick arg.down) fun reply => pure (ULift.up reply)
    | .capture, _ => vis .capture fun reply => pure (PUnit.unit, ULift.up reply)

private def instr : Primitive Event Opcode Runtime
  | .seed, .atom arg => vis (.call .seed arg.2.down) fun reply => pure (atom reply)
  | .tick, .atom arg => vis (.call .tick arg.2.down) fun reply => pure (atom reply)
  | .capture, .unit => vis .capture fun reply => pure (.pair .unit (atom reply))
  | op, _ => vis (.malformed op) Empty.elim

example : Compatible (κ' := SortName) typed instr := by
  intro op arg
  cases op with
  | seed =>
    change (vis (.call .seed arg.down) fun reply => pure (atom reply)) =
      ((vis (.call .seed arg.down) (fun reply => pure (ULift.up reply)) : Tree Event Atom) >>=
        fun v => pure (atom v.down))
    simp only [vis_bind, pure_bind]
  | tick =>
    change (vis (.call .tick arg.down) fun reply => pure (atom reply)) =
      ((vis (.call .tick arg.down) (fun reply => pure (ULift.up reply)) : Tree Event Atom) >>=
        fun v => pure (atom v.down))
    simp only [vis_bind, pure_bind]
  | capture =>
    change (vis .capture fun reply => pure (Value.pair .unit (atom reply))) =
      ((vis .capture (fun reply => pure (PUnit.unit, ULift.up reply)) : Tree Event (PUnit × Atom)) >>=
        fun v => pure (Value.pair .unit (atom v.2.down)))
    simp only [vis_bind, pure_bind]

private def reg : Reg := ⟨()⟩
private def header : Label := ⟨10⟩
private def back : Label := ⟨20⟩
private def exitLabel : Label := ⟨99⟩

private def source : CFG Reg Label Opcode :=
  ⟨.let1 reg (.app .seed (.var reg)) (.term (.br header (.var reg))),
    [(header, ⟨reg, .term (.br back (.var reg))⟩),
     (back, ⟨reg, .let1 reg (.app .tick (.var reg)) (.term (.br header (.var reg)))⟩)]⟩

private def names : Fin 1 → Reg := fun _ => reg
private abbrev generated := CFG.Cyclic.Versioning.compile source

private def admitted := (compileTyped source [exitLabel] names captures
  (fun _ => edgeType) (fun _ => num)).get (by decide)

private def store (capture : Nat) : Reg × Nat → Value Runtime := fun _ => atom capture
private def env (capture : Nat) : Env Runtime := fun _ => atom capture
private def ambient : Env Runtime := fun _ => .unit
private def packet (n : Nat) : Value Runtime := .pair (atom n) .unit

private def packetRead : LetCase.LocallyNameless.Tm Empty Opcode 0 := .op .capture .unit

private def closed := (Capture.close captures (fun _ => edgeType) (fun _ => num)
  admitted.val admitted.property.2 packetRead
  (show LetCase.LocallyNameless.HasType Opcode .nil .nil packetRead inputType from .op .unit)).get (by decide)

private theorem entry_requests (capture : Nat) :
    region instr (env capture) admitted.val.entry.erase =
      vis (.call .seed capture) (fun reply => pure (0, packet reply)) := by
  change region instr (env capture)
    (.let₁ (.op .seed (.var 0)) (.br 0 (.pair (.var 0) .unit))) = _
  simp only [region, LambdaSSA.Semantics.Interaction.term, pure_bind, vis_bind, env, instr,
    LambdaSSA.Semantics.extend_zero, packet, atom]

example (capture : Nat) :
    (generated.entry.evalJump (treeModel instr) (store capture) >>=
      fun p => pure (treeNumber (labelIndex generated.blocks [exitLabel]) p)) =
      vis (.call .seed capture) (fun reply => pure (0, packet reply)) :=
  (entry_tree instr generated [exitLabel] (fun i => (names i, 0)) admitted.property.1
    (store capture) (env capture) (fun _ => rfl)).trans (entry_requests capture)

private def backIndex : Fin generated.blocks.length := ⟨1, by decide⟩

private theorem back_requests (capture argument : Nat) :
    region instr (extend (env capture) (packet argument)) (admitted.val.block backIndex).erase =
      vis (.call .tick argument) (fun reply => pure (0, packet reply)) := by
  change region instr (extend (env capture) (packet argument))
    (.let₂ (.var 0) (.let₁ (.op .tick (.var 1)) (.br 0 (.pair (.var 0) .unit)))) = _
  simp only [region, LambdaSSA.Semantics.Interaction.term, pure_bind, vis_bind, packet, instr, atom,
    LambdaSSA.Semantics.extend_zero, LambdaSSA.Semantics.extend_succ]

example (capture argument : Nat) :
    (CFG.Cyclic.stepSSA (treeModel instr) generated.blocks (store capture) (back, packet argument) >>=
      fun s => pure (s.map id (treeNumber (labelIndex generated.blocks [exitLabel])))) =
      vis (.call .tick argument) (fun reply => pure (.inr (0, packet reply))) := by
  rw [step_tree instr generated [exitLabel] (fun i => (names i, 0)) admitted.property.1
    back backIndex rfl (store capture) (env capture) (packet argument), back_requests, vis_bind]
  simp only [pure_bind]

-- Reading the exact capture packet exposes a request. Its reply becomes the
-- seed request's operand, and the seed reply becomes the first edge packet.
private theorem closed_entry_requests : region instr ambient closed.val.entry.erase =
    vis (.capture) (fun captured =>
      vis (.call .seed captured) (fun reply => pure (0, packet reply))) := by
  change region instr ambient
    (.let₁ (.op .capture .unit) (.let₂ (.var 0)
      (.let₁ (.op .seed (.var 0)) (.br 0 (.pair (.var 0) .unit))))) = _
  simp only [region, LambdaSSA.Semantics.Interaction.term, pure_bind, vis_bind, packet, instr, atom,
    LambdaSSA.Semantics.extend_zero]

example (capture : Nat) :
    (CFG.Cyclic.runSSA (M := ModelTree Event) (treeModel instr) generated (store capture) >>=
      fun p => pure (treeExitNumber [exitLabel] p)) = region instr (env capture) admitted.val.erase :=
  compile_run_tree instr source [exitLabel] names admitted.property.1
    (store capture) (env capture) (fun _ => rfl)

private theorem block_environment (i : Fin 2) (v : Value Runtime) (capture : Nat) :
    region instr (extend ambient v) (admitted.val.block i).erase =
      region instr (extend (env capture) v) (admitted.val.block i).erase := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => k.elim0) j) i
  · change region instr (extend ambient v) (.let₂ (.var 0) (.br 1 (.pair (.var 1) .unit))) =
      region instr (extend (env capture) v) (.let₂ (.var 0) (.br 1 (.pair (.var 1) .unit)))
    cases v <;> rfl
  · change region instr (extend ambient v)
        (.let₂ (.var 0) (.let₁ (.op .tick (.var 1)) (.br 0 (.pair (.var 0) .unit)))) =
      region instr (extend (env capture) v)
        (.let₂ (.var 0) (.let₁ (.op .tick (.var 1)) (.br 0 (.pair (.var 0) .unit))))
    cases v <;> rfl

private noncomputable def openStep (capture : Nat) (p : BlockInput Runtime 2) :
    Tree Event (Transfer Runtime ⊕ BlockInput Runtime 2) :=
  region instr (extend (env capture) p.2) (admitted.val.block p.1).erase >>=
    fun out => pure (splitTransfer 2 out)

private noncomputable def closedStep (p : BlockInput Runtime 2) :
    Tree Event (Transfer Runtime ⊕ BlockInput Runtime 2) :=
  region instr (extend ambient p.2) (closed.val.block p.1).erase >>=
    fun out => pure (splitTransfer 2 out)

private theorem closed_tree :
    region instr ambient closed.val.erase =
      vis .capture (fun capture => region instr (env capture) admitted.val.erase) := by
  have sameSteps (capture : Nat) : closedStep = openStep capture := by
    funext p
    unfold closedStep openStep
    rw [closed.property.2.block p.1, block_environment]
  change (region instr ambient closed.val.entry.erase >>= fun out =>
      Sum.elim pure (iter closedStep) (splitTransfer 2 out)) =
    vis .capture (fun capture => region instr (env capture) admitted.val.entry.erase >>= fun out =>
      Sum.elim pure (iter (openStep capture)) (splitTransfer 2 out))
  rw [closed_entry_requests, vis_bind]
  congr 1
  funext capture
  rw [entry_requests, sameSteps capture]

-- The checked packing theorem observes exactly the named runner after the
-- capture reply, with the dispatcher's exit encoding applied to its return.
example : region instr ambient (packedExecutionRegion closed.property.1) =
    vis .capture (fun capture => CFG.Cyclic.runSSA (M := ModelTree Event) (treeModel instr) generated (store capture) >>=
      fun p => pure (packedTreeOutput (treeExitNumber [exitLabel] p))) := by
  rw [packedExecution_tree, closed_tree, vis_bind]
  congr 1
  funext capture
  rw [← compile_run_tree instr source [exitLabel] names admitted.property.1
    (store capture) (env capture) (fun _ => rfl), bind_assoc]
  simp only [pure_bind]

private theorem tick_loop (capture argument : Nat) :
    iter (openStep capture) (0, packet argument) =
      vis (.call .tick argument) (fun reply => iter (openStep capture) (0, packet reply)) := by
  have headerStep : openStep capture (0, packet argument) = pure (.inr (1, packet argument)) := by
    change (region instr (extend (env capture) (packet argument))
      (.let₂ (.var 0) (.br 1 (.pair (.var 1) .unit))) >>= _) = _
    simp only [region, LambdaSSA.Semantics.Interaction.term, pure_bind, packet,
      LambdaSSA.Semantics.extend_zero, LambdaSSA.Semantics.extend_succ]
    rfl
  have backStep : openStep capture (1, packet argument) =
      vis (.call .tick argument) (fun reply => pure (.inr (0, packet reply))) := by
    change (region instr (extend (env capture) (packet argument)) (admitted.val.block backIndex).erase >>= _) = _
    rw [back_requests, vis_bind]
    simp only [pure_bind]
    rfl
  calc
    _ = iter (openStep capture) (1, packet argument) := by
      rw [congrFun (iterate_fixpoint (openStep capture)) (0, packet argument)]
      rw [headerStep, pure_bind, Sum.elim_inr]
    _ = _ := by
      rw [congrFun (iterate_fixpoint (openStep capture)) (1, packet argument)]
      rw [backStep]
      simp only [vis_bind, pure_bind, Sum.elim_inr]

-- Two successive tick requests use the seed reply and then the first tick
-- reply as operands. The equality quantifies over all replies at each node.
example : region instr ambient (packedExecutionRegion closed.property.1) =
    vis .capture (fun capture => vis (.call .seed capture) (fun seed =>
      vis (.call .tick seed) (fun first =>
        vis (.call .tick first) (fun second => iter (openStep capture) (0, packet second) >>=
          fun p => pure (packedTreeOutput p))))) := by
  rw [packedExecution_tree, closed_tree, vis_bind]
  congr 1
  funext capture
  change ((region instr (env capture) admitted.val.entry.erase >>= fun out =>
      Sum.elim pure (iter (openStep capture)) (splitTransfer 2 out)) >>= _) = _
  rw [entry_requests]
  simp only [vis_bind, pure_bind]
  congr 1
  funext seed
  change (iter (openStep capture) (0, packet seed) >>= _) = _
  rw [tick_loop, vis_bind]
  congr 1
  funext first
  rw [tick_loop, vis_bind]

end Silmaril.Isotope.Bridge.NamedFlat.Interaction.Examples
