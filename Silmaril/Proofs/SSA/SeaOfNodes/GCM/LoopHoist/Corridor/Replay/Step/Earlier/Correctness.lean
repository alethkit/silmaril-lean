module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix.Insert.Thms
import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Block Cfg Terminator)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier
open AfterReorder.Second (Candidate checkPrefixCut)
open AfterReorder.Second.Emit (emitAt? liftCode liftCode_eval rewriteAt?)
open Loop.MLIR.CF (Program TargetOp evalOp model lower_run)

variable {Input extra : List Width} {saved carried result : Width}
variable {state : Step.State Input saved carried result extra} {request : Nomination}
variable {moved : Emission Input saved carried result extra}

theorem emit?_spec (accepted : emit? state request = some moved) :
    request.cut < (extra ++ [saved]).length ∧
    Step.emit state { request with cut := (extra ++ [saved]).length } = .ok moved.append ∧
    checkPrefixCut state.cfg moved.append.candidate request.cut = true ∧
    ∃ leading, Saved.splitPrefix? state.cfg.entry (extra ++ [saved]) = some (leading, moved.tail) ∧
      leading.insert? moved.append.candidate.op ((extra ++ [saved]).length - request.cut)
        moved.append.candidate.inputs = some moved.splice := by
  simp only [emit?] at accepted
  split at accepted
  next earlier =>
    split at accepted
    next appended appendAt =>
      split at accepted
      next checked =>
        obtain ⟨⟨leading, tail⟩, split, rest⟩ := Option.bind_eq_some_iff.mp accepted
        obtain ⟨splice, inserted, result⟩ := Option.bind_eq_some_iff.mp rest
        cases result
        exact ⟨earlier, appendAt, checked, leading, split, inserted⟩
      next => cases accepted
    next => cases accepted
  next => cases accepted

private theorem append_entry {candidate : Candidate Input saved carried result extra}
    {index : Nat} {target : Cfg TargetOp (Label saved carried result (candidate.width :: extra)) Input [result]}
    {leading : Saved.Prefix Input ((extra ++ [saved]) ++ Input)}
    {tail : Block TargetOp (Label saved carried result extra) ((extra ++ [saved]) ++ Input) [result]}
    (split : Saved.splitPrefix? state.cfg.entry (extra ++ [saved]) = some (leading, tail))
    (emitted : emitAt? state.cfg index candidate.op candidate.inputs = some target) :
    target.entry = leading.wrap (.letOp candidate.op candidate.inputs (liftCode Var.there .here tail)) := by
  cases rewritten : rewriteAt? (consumer := candidate.width) index Var.there .here (state.cfg.block .header) with
  | none => simp [emitAt?, split, rewritten] at emitted
  | some header =>
    cases exit : state.cfg.block .exit with
    | letOp => simp [emitAt?, split, rewritten, exit] at emitted
    | terminator term =>
      cases term with
      | br => simp [emitAt?, split, rewritten, exit] at emitted
      | condBr => simp [emitAt?, split, rewritten, exit] at emitted
      | ret returns =>
        simp [emitAt?, split, rewritten, exit] at emitted
        cases emitted
        rfl

private theorem liftCode_targets {Γ Δ Θ : List Width} {w : Width}
    (code : Block TargetOp (Label saved carried result extra) Γ [result])
    (rename : Rename Γ Δ) (keep : Var Δ w) (other : Rename Γ Θ) (otherKeep : Var Θ w) :
    (shape.ofBlock (liftCode rename keep code)).target = (shape.ofBlock (liftCode other otherKeep code)).target := by
  induction code generalizing Δ Θ with
  | letOp op operands rest ih => exact ih (under rename) (.there keep) (under other) (.there otherKeep)
  | terminator term =>
    cases term with
    | ret => rfl
    | br edge =>
      rcases edge with ⟨label, _⟩
      funext slot
      cases label <;> cases slot <;> rfl
    | condBr test onTrue onFalse =>
      rcases onTrue with ⟨positive, _⟩
      rcases onFalse with ⟨negative, _⟩
      funext slot
      cases positive <;> cases negative <;> cases slot <;> rfl

private theorem wrap_targets {Γ newExtra : List Width}
    (leading : Saved.Prefix Input Γ) (tail : Block TargetOp (Label saved carried result newExtra) Γ [result]) :
    (shape.ofBlock (leading.wrap tail)).target = (shape.ofBlock tail).target := by
  induction leading with
  | nil => rfl
  | snoc prior op operands ih => exact ih (.letOp op operands tail)

theorem emit?_entry_targets (accepted : emit? state request = some moved) :
    (shape moved.cfg none).target = (shape moved.append.next.cfg none).target := by
  obtain ⟨_, appended, _, leading, split, _⟩ := emit?_spec accepted
  change (shape.ofBlock (moved.splice.leading.wrap (liftCode moved.splice.previous moved.splice.inserted moved.tail))).target =
    (shape.ofBlock moved.append.next.cfg.entry).target
  rw [append_entry split (Step.emit_spec appended).2.2.2.2.1, wrap_targets, wrap_targets]
  exact liftCode_targets moved.tail moved.splice.previous moved.splice.inserted Var.there .here

theorem emit?_entry_eq (accepted : emit? state request = some moved) (input : Env Input) :
    moved.cfg.entry.eval evalOp (fun term env => Terminator.eval env term) input =
      moved.append.next.cfg.entry.eval evalOp (fun term env => Terminator.eval env term) input := by
  obtain ⟨_, appended, _, leading, split, inserted⟩ := emit?_spec accepted
  rw [append_entry split (Step.emit_spec appended).2.2.2.2.1]
  let old := leading.eval input
  let physical := moved.splice.leading.eval input
  let value := evalOp moved.append.candidate.op (moved.append.candidate.inputs.eval old)
  have same {width : Width} (ref : Var _ width) := Saved.Prefix.insert?_eval inserted input ref
  have kept : physical.get moved.splice.inserted = value := same .here
  have reads : ∀ {width} (ref : Var _ width), physical.get (moved.splice.previous ref) = old.get ref :=
    fun ref => same (.there ref)
  change (moved.splice.leading.wrap (liftCode moved.splice.previous moved.splice.inserted moved.tail)).eval
    evalOp (fun term env => Terminator.eval env term) input = _
  rw [Saved.Prefix.wrap_eval, Saved.Prefix.wrap_eval, liftCode_eval _ _ _ _ _ reads, kept]
  exact (liftCode_eval moved.tail Var.there .here old (.cons value old) (fun _ => rfl)).symm

theorem emit?_routes (accepted : emit? state request = some moved)
    {input : Env Input} {values : Env (extra ++ [saved])}
    (matched : Saved.Prefix.Matches state.cfg.entry input values) :
    Saved.StepRoutes state.cfg moved.cfg input values
      (evalOp moved.append.candidate.op (moved.append.candidate.inputs.eval (values.append input))) := by
  obtain ⟨_, _, found, _, emitted, _, _⟩ := Step.emit_spec (emit?_spec accepted).2.1
  have routes := (AfterReorder.Second.Emit.emitAt?_step matched found emitted).1
  exact ⟨(emit?_entry_eq accepted input).trans routes.entry, routes.block⟩

theorem emit?_run_eq (accepted : emit? state request = some moved) (input : Env Input) (fuel : Nat) :
    moved.cfg.run evalOp fuel input = moved.append.next.cfg.run evalOp fuel input := by
  have common : ∀ (budget : Nat) {Γ : List Width}
      (code : Block TargetOp (Label saved carried result (moved.append.candidate.width :: extra)) Γ [result])
      (env : Env Γ),
      moved.cfg.runBlock evalOp input budget code env =
        moved.append.next.cfg.runBlock evalOp input budget code env := by
    intro budget
    induction budget with
    | zero => intros; rfl
    | succ budget ih =>
      intro Γ code env
      simp only [Cfg.runBlock]
      split
      · exact ih _ _
      · rfl
  cases fuel with
  | zero => rfl
  | succ fuel =>
    simp only [Cfg.run, Cfg.runBlock, emit?_entry_eq accepted input]
    split
    · exact common _ _ _
    · rfl

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
theorem emit?_denotePart (accepted : emit? state request = some moved) (input : Env Input) :
    (Cfg.embed moved.cfg).denotePart evalOp input =
      (Cfg.embed moved.append.next.cfg).denotePart evalOp input := by
  apply Part.ext
  intro value
  simp only [Cfg.mem_denotePart_iff, Cfg.embed_run, emit?_run_eq accepted]

theorem emit?_fromTwo_budget {entrySigs headerSigs : List (List (Diamond.Ty Width))}
    {g : Program Input carried result entrySigs headerSigs}
    {header : List Header.Pair.Request} {first : First Input carried result} {producer consumer : Nomination}
    {two : AfterReorder.Second.Emit.Emission Input carried result}
    {moved : Emission Input two.prepared.intermediate.1 carried result [two.prepared.consumer.width]}
    (seed : replay g header [producer, consumer] = .ok (.two first consumer two))
    (accepted : emit? (Step.fromTwo first consumer two) request = some moved)
    (input : Env Input) (budget : Nat) :
    moved.cfg.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) := by
  have appended : Step.emit (Step.fromTwo first consumer two) { request with cut := 2 } = .ok moved.append :=
    (emit?_spec accepted).2.1
  have continued : Step.run (Step.fromTwo first consumer two) 2
      [{ request with cut := 2 }] = .ok ⟨_, moved.append.next⟩ := by
    simp [Step.run, appended]
  exact (emit?_run_eq accepted input _).trans
    ((Step.fromTwo_run_eq seed continued input _).trans (lower_run g input budget))

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier
