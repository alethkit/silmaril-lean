module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix.Insert.Thms
import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Terminator)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow
open AfterReorder.Second (checkPrefixCut findCaptured?)
open AfterReorder.Second.Emit (emitAt?_entry liftCode liftCode_eval liftCode_targets_congr)
open Loop.MLIR.CF (Program evalOp model lower_run)

variable {Input extra : List Width} {saved carried result : Width}
variable {state : Step.State Input saved carried result extra} {first second : Nomination}
variable {prior : Step.Earlier.Emission Input saved carried result extra} {moved : Emission prior}

theorem savedCount_eq (firstDone : Step.Earlier.emit? state first = some prior) :
    savedCount prior = ((CurrentExtra prior) ++ [saved]).length := by
  obtain ⟨_, _, _, _, _, splice⟩ := Step.Earlier.emit?_spec firstDone
  rw [savedCount, Saved.Prefix.insert?_length splice]
  simp only [List.length_append, List.length_cons]
  omega

theorem emit?_spec (accepted : emit? prior second = some moved) :
    Step.emit prior.append.next { second with cut := ((CurrentExtra prior) ++ [saved]).length } = .ok moved.append ∧
    checkPrefixCut prior.cfg (atLayout prior moved.append.candidate) second.cut = true ∧
    prior.splice.leading.insert? moved.append.candidate.op (savedCount prior - second.cut)
      (physicalOperands prior moved.append.candidate) = some moved.splice := by
  simp only [emit?] at accepted
  split at accepted
  next appended produced =>
    split at accepted
    next checked =>
      obtain ⟨splice, inserted, result⟩ := Option.bind_eq_some_iff.mp accepted
      cases result
      exact ⟨produced, checked, inserted⟩
    next => cases accepted
  next => cases accepted

theorem emit?_placement (accepted : emit? prior second = some moved) :
    prior.append.next.origins[moved.append.index]? = some second.origin ∧
    findCaptured? moved.append.index 0 (Saved.origins ((CurrentExtra prior) ++ [saved]))
      (prior.cfg.block .header) = some moved.append.candidate ∧
    Legal prior.cfg (atLayout prior moved.append.candidate).operands moved.append.candidate.uses ⟨none, second.cut⟩ ∧
    moved.splice.inserted.index = savedCount prior - second.cut := by
  obtain ⟨appended, checked, inserted⟩ := emit?_spec accepted
  obtain ⟨_, located, found, _, _, _, _⟩ := Step.emit_spec appended
  exact ⟨located, found, AfterReorder.Second.checkPrefixCut_legal checked, (Saved.Prefix.insert?_indices inserted).1⟩

theorem emit?_append_replay (firstDone : Step.Earlier.emit? state first = some prior)
    (accepted : emit? prior second = some moved) (position : Nat) :
    Step.run state position [{ first with cut := (extra ++ [saved]).length },
      { second with cut := ((CurrentExtra prior) ++ [saved]).length }] = .ok ⟨_, moved.append.next⟩ := by
  simp only [Step.run, (Step.Earlier.emit?_spec firstDone).2.1, (emit?_spec accepted).1]

theorem physicalOperands_eval (firstDone : Step.Earlier.emit? state first = some prior) (input : Env Input) :
    ∃ leading tail,
      Saved.splitPrefix? prior.append.next.cfg.entry ((CurrentExtra prior) ++ [saved]) = some (leading, tail) ∧
      ∀ candidate : AfterReorder.Second.Candidate Input saved carried result (CurrentExtra prior),
        (physicalOperands prior candidate).eval (prior.splice.leading.eval input) =
          candidate.inputs.eval (leading.eval input) := by
  obtain ⟨leading, tail, split, reads⟩ := Step.Earlier.emit?_prefix_agree firstDone
  exact ⟨leading, tail, split, fun candidate => evalRenameOperands prior.splice.toPhysical _ _
    (reads input) candidate.inputs⟩

theorem emit?_entry_targets (firstDone : Step.Earlier.emit? state first = some prior)
    (accepted : emit? prior second = some moved) :
    (shape moved.cfg none).target = (shape moved.append.next.cfg none).target := by
  obtain ⟨leading, tail, split, _⟩ := Step.Earlier.emit?_prefix_agree firstDone
  have emitted := (Step.emit_spec (emit?_spec accepted).1).2.2.2.2.1
  have entry := Step.Earlier.emit?_entry_targets firstDone
  change (shape.ofBlock (prior.splice.leading.wrap prior.entryTail)).target =
    (shape.ofBlock prior.append.next.cfg.entry).target at entry
  rw [← Saved.splitPrefix?_wrap split, Saved.Prefix.wrap_targets, Saved.Prefix.wrap_targets] at entry
  change (shape.ofBlock (moved.splice.leading.wrap (liftCode moved.splice.previous moved.splice.inserted prior.entryTail))).target =
    (shape.ofBlock moved.append.next.cfg.entry).target
  rw [emitAt?_entry split emitted, Saved.Prefix.wrap_targets, Saved.Prefix.wrap_targets]
  exact liftCode_targets_congr prior.entryTail tail moved.splice.previous moved.splice.inserted Var.there .here entry

theorem emit?_entry_eq (firstDone : Step.Earlier.emit? state first = some prior)
    (accepted : emit? prior second = some moved) (input : Env Input) :
    moved.cfg.entry.eval evalOp (fun term env => Terminator.eval env term) input =
      moved.append.next.cfg.entry.eval evalOp (fun term env => Terminator.eval env term) input := by
  obtain ⟨appended, _, inserted⟩ := emit?_spec accepted
  obtain ⟨leading, tail, split, args⟩ := physicalOperands_eval firstDone input
  have emitted := (Step.emit_spec appended).2.2.2.2.1
  let old := prior.splice.leading.eval input
  let physical := moved.splice.leading.eval input
  let value := evalOp moved.append.candidate.op (moved.append.candidate.inputs.eval (leading.eval input))
  have same {w : Width} (ref : Var _ w) := Saved.Prefix.insert?_eval inserted input ref
  have kept : physical.get moved.splice.inserted = value := (same .here).trans
    (congrArg (evalOp moved.append.candidate.op) (args moved.append.candidate))
  have reads : ∀ {w} (ref : Var _ w), physical.get (moved.splice.previous ref) = old.get ref :=
    fun ref => same (.there ref)
  calc
    _ = (prior.cfg.entry.eval evalOp (fun term env => Terminator.eval env term) input).map
        (Saved.prependFrame value) id := by
      change (moved.splice.leading.wrap (liftCode moved.splice.previous moved.splice.inserted prior.entryTail)).eval
        evalOp (fun term env => Terminator.eval env term) input = _
      rw [Saved.Prefix.wrap_eval, liftCode_eval _ _ _ _ _ reads, kept]
      change _ = (prior.splice.leading.wrap prior.entryTail |>.eval evalOp
        (fun term env => Terminator.eval env term) input).map (Saved.prependFrame value) id
      rw [Saved.Prefix.wrap_eval]
    _ = _ := by
      rw [Step.Earlier.emit?_entry_eq firstDone input, ← Saved.splitPrefix?_wrap split,
        emitAt?_entry split emitted, Saved.Prefix.wrap_eval, Saved.Prefix.wrap_eval]
      exact (liftCode_eval tail Var.there .here (leading.eval input) (.cons value (leading.eval input))
        (fun _ => rfl)).symm

theorem emit?_routes (firstDone : Step.Earlier.emit? state first = some prior)
    (accepted : emit? prior second = some moved)
    {input : Env Input} {values : Env (extra ++ [saved])}
    (matched : Saved.Prefix.Matches state.cfg.entry input values) :
    let firstValue := evalOp prior.append.candidate.op (prior.append.candidate.inputs.eval (values.append input))
    let nextValues := Env.cons firstValue values
    let nextValue := evalOp moved.append.candidate.op (moved.append.candidate.inputs.eval (nextValues.append input))
    Saved.StepRoutes state.cfg prior.cfg input values firstValue ∧
      Saved.StepRoutes prior.cfg moved.cfg input nextValues nextValue := by
  obtain ⟨_, _, foundFirst, _, emittedFirst, _, _⟩ := Step.emit_spec (Step.Earlier.emit?_spec firstDone).2.1
  obtain ⟨_, _, foundNext, _, emittedNext, _, _⟩ := Step.emit_spec (emit?_spec accepted).1
  have matchedAppend := (AfterReorder.Second.Emit.emitAt?_step matched foundFirst emittedFirst).2
  have next := (AfterReorder.Second.Emit.emitAt?_step matchedAppend foundNext emittedNext).1
  refine ⟨Step.Earlier.emit?_routes firstDone matched, ⟨?_, next.block⟩⟩
  rw [emit?_entry_eq firstDone accepted input, Step.Earlier.emit?_entry_eq firstDone input]
  exact next.entry

theorem emit?_run_eq (firstDone : Step.Earlier.emit? state first = some prior)
    (accepted : emit? prior second = some moved) (input : Env Input) (fuel : Nat) :
    moved.cfg.run evalOp fuel input = moved.append.next.cfg.run evalOp fuel input :=
  Step.Earlier.run_eq_of_entry _ _ input fuel (emit?_entry_eq firstDone accepted input) (fun _ => rfl)

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
theorem emit?_denotePart (firstDone : Step.Earlier.emit? state first = some prior)
    (accepted : emit? prior second = some moved) (input : Env Input) :
    (Cfg.embed moved.cfg).denotePart evalOp input =
      (Cfg.embed moved.append.next.cfg).denotePart evalOp input := by
  apply Part.ext
  intro value
  simp only [Cfg.mem_denotePart_iff, Cfg.embed_run, emit?_run_eq firstDone accepted]

theorem emit?_fromTwo_budget {entrySigs headerSigs : List (List (Diamond.Ty Width))}
    {g : Program Input carried result entrySigs headerSigs}
    {header : List Header.Pair.Request} {record : First Input carried result} {producer consumer : Nomination}
    {two : AfterReorder.Second.Emit.Emission Input carried result}
    {prior : Step.Earlier.Emission Input two.prepared.intermediate.1 carried result [two.prepared.consumer.width]}
    {moved : Emission prior}
    (seed : replay g header [producer, consumer] = .ok (.two record consumer two))
    (firstDone : Step.Earlier.emit? (Step.fromTwo record consumer two) first = some prior)
    (accepted : emit? prior second = some moved) (input : Env Input) (budget : Nat) :
    moved.cfg.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) := by
  exact (emit?_run_eq firstDone accepted input _).trans
    ((Step.fromTwo_run_eq seed (emit?_append_replay firstDone accepted 2) input _).trans (lower_run g input budget))

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow
