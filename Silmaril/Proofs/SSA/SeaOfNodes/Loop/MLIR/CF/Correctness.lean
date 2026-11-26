module

public import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Thms
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.SSA.SeaOfNodes.MLIR.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Proofs

open Diamond (Val ValueSort dataPorts)
open RVSDG (Tuple extend)
open SeaOfNodes.MLIR (Word sourceInputs)
open SeaOfNodes.MLIR.Lowering
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Cfg Frame Terminator)
open Silmaril.MLIR.CF.SwitchAssert (Outcome)

variable {Γ : List Width} {carried result : Width} {entrySigs headerSigs : List (List (Diamond.Ty Width))}

private theorem opcode_correct {ins : List (ValueSort Width)} {out : ValueSort Width}
    (op : Op ins out) (input : Tuple (Val Word) (dataPorts ins)) :
    evalOp (opcode op) (encodeValues input) = valueBits (model.run op input) := by
  cases op with
  | arithmetic op =>
    cases op with
    | constant => cases input; rfl
    | binary op =>
      cases input with | cons x tail =>
      cases tail with | cons y tail =>
      cases tail
      cases op <;> rfl
  | ult =>
    cases input with | cons x tail =>
    cases tail with | cons y tail =>
    cases tail
    rfl

private theorem append_names {Δ : List Width} {left right : List (Diamond.Ty Width)}
    {env : Env Δ} {names : Tuple (Names Δ) left} {values : Tuple (Val Word) left}
    {suffix : Tuple (Names Δ) right} {tail : Tuple (Val Word) right}
    (first : NamesAgree env names values) (last : NamesAgree env suffix tail) :
    NamesAgree env (appendTuple suffix names) (appendTuple tail values) := by
  induction names with
  | nil => cases values; exact last
  | cons name names ih =>
    cases values with
    | cons value values =>
      intro s port
      cases port with
      | head => exact first .head
      | tail port => exact ih (fun pos => first (.tail pos)) port

private def latchValue (value : Word carried) : Tuple (Val Word) (dataPorts [.data carried]) :=
  .cons value .nil

private def headerFrame (value : Word carried) : Frame (Label carried result) :=
  ⟨.header, .cons value .nil⟩

private def exitFrame (value : Word result) : Frame (Label carried result) :=
  ⟨.exit, .cons value .nil⟩

private def resultEnv (value : Word result) : Env [result] :=
  .cons value .nil

private def stepFrame : Word result ⊕ Tuple (Val Word) (dataPorts [.data carried]) →
    Frame (Label carried result)
  | .inl value => exitFrame value
  | .inr next => headerFrame (next.get .head)

variable (g : Program Γ carried result entrySigs headerSigs) (input : Env Γ)

private theorem entry_eval :
    (lower g).entry.eval evalOp (fun term env => term.eval env) input =
      .inl (headerFrame ((g.initial model (sourceInputs input)).get .head)) := by
  refine lowerCode_eval opcode evalOp model.run opcode_correct g.preheader _ input (sourceInputs input) PUnit.unit
    ⟨inputs_agree input, trivial⟩ (entryTerm g) (fun term env => term.eval env) _ ?_
  intro Δ scope env ok
  have wire := (ok.resolve ((g.phiInputs .entry).get .head)).trans
    (g.latch_get model .entry (sourceInputs input) (g.preheader.eval model (sourceInputs input) PUnit.unit) .head).symm
  exact congrArg (fun v => Sum.inl (headerFrame v)) wire

private theorem header_eval (old : Word carried) :
    ((lower g).block .header).eval evalOp (fun term env => term.eval env) (.cons old input) =
      .inl (stepFrame (g.step model (sourceInputs input) (latchValue old))) := by
  let args := appendTuple (latchValue old) (sourceInputs input)
  have bindings : (headerScope Γ carried).Agrees (.cons old input) args PUnit.unit :=
    ⟨append_names (weaken_names (inputs_agree input) old) (by
      intro s p
      cases p with
      | head => rfl
      | tail p => cases p), trivial⟩
  refine lowerCode_eval opcode evalOp model.run opcode_correct g.header _ _ args _ bindings
    (headerTerm g) (fun term env => term.eval env) _ ?_
  intro Δ scope env ok
  let locals := g.header.eval model args PUnit.unit
  have testBit (b : Bool) : (BitVec.ofBool b).getLsbD 0 = b := by cases b <;> rfl
  have guard : (env.get (scope.resolveValue g.predicate)).getLsbD 0 =
      (Diamond.read model g.predicate args locals).down :=
    (congrArg (fun bits : BitVec 1 => bits.getLsbD 0) (ok.resolve g.predicate)).trans
      (testBit (Diamond.read model g.predicate args locals).down)
  have update : env.get (scope.resolveValue ((g.phiInputs .backedge).get .head)) =
      (g.latch model .backedge args locals).get .head :=
    (ok.resolve ((g.phiInputs .backedge).get .head)).trans
      (g.latch_get model .backedge args locals .head).symm
  have readback : env.get (scope.resolveValue g.result) = Diamond.read model g.result args locals :=
    ok.resolve g.result
  change Sum.inl (if (env.get (scope.resolveValue g.predicate)).getLsbD 0 then
      headerFrame (env.get (scope.resolveValue ((g.phiInputs .backedge).get .head)))
    else exitFrame (env.get (scope.resolveValue g.result))) = _
  rw [guard, update, readback]
  have route (test : Bool) (next : Tuple (Val Word) (dataPorts [.data carried])) (out : Word result) :
      (if test then headerFrame (next.get .head) else exitFrame out) =
        stepFrame (if test then .inr next else .inl out) := by
    cases test <;> rfl
  exact congrArg Sum.inl (route _ _ _)

private theorem run_entry (fuel : Nat) :
    (lower g).run evalOp (fuel + 1) input =
      (lower g).runFrom evalOp fuel input (headerFrame ((g.initial model (sourceInputs input)).get .head)) := by
  unfold Cfg.run
  rw [Cfg.runBlock, entry_eval]
  rfl

private theorem run_header (fuel : Nat) (old : Word carried) :
    (lower g).runFrom evalOp (fuel + 1) input (headerFrame old) =
      (lower g).runFrom evalOp fuel input (stepFrame (g.step model (sourceInputs input) (latchValue old))) := by
  change (lower g).runBlock evalOp input (fuel + 1) ((lower g).block .header) (.cons old input) = _
  rw [Cfg.runBlock, header_eval]
  rfl

private theorem run_header_budget (budget : Nat) (old : Word carried) :
    (lower g).runFrom evalOp (budget + 2) input (headerFrame old) =
      (g.evalFrom model (sourceInputs input) budget (latchValue old)).map resultEnv := by
  induction budget generalizing old with
  | zero =>
    erw [Graph.evalFrom.eq_1 g model (sourceInputs input) (latchValue old)]
    rw [show 0 + 2 = 1 + 1 by rfl, run_header]
    cases g.step model (sourceInputs input) (latchValue old) with
    | inl value => rfl
    | inr next => exact run_header g input 0 (next.get .head)
  | succ fuel ih =>
    erw [Graph.evalFrom.eq_2 g model (sourceInputs input) (latchValue old) fuel]
    rw [show fuel + 1 + 2 = (fuel + 2) + 1 by rfl, run_header]
    cases g.step model (sourceInputs input) (latchValue old) with
    | inl value => rfl
    | inr next =>
      cases next with
      | cons value tail =>
        cases tail
        exact ih value

theorem run_budget (budget : Nat) :
    (lower g).run evalOp (budget + 3) input =
      (g.evalBackedges model budget (sourceInputs input)).map (fun value => Env.cons value .nil) := by
  erw [show budget + 3 = (budget + 2) + 1 by rfl, run_entry, run_header_budget]
  unfold Graph.evalBackedges
  cases g.initial model (sourceInputs input) with
  | cons value tail => cases tail; rfl

theorem returns_iff (value : Word result) :
    g.Returns model (sourceInputs input) value ↔
      ∃ fuel, (lower g).run evalOp fuel input = some (.cons value .nil) := by
  refine (g.returns_iff_evalBackedges model (sourceInputs input) value).trans ?_
  constructor
  · rintro ⟨budget, run⟩
    exact ⟨budget + 3, by rw [run_budget, run]; rfl⟩
  · rintro ⟨fuel, run⟩
    rcases fuel with _ | fuel
    · cases run
    rcases fuel with _ | fuel
    · rw [run_entry] at run
      cases run
    rcases fuel with _ | budget
    · erw [run_entry, run_header] at run
      cases run
    erw [run_budget, Option.map_eq_some_iff] at run
    obtain ⟨other, observed, same⟩ := run
    exact ⟨budget, observed.trans (congrArg (fun env : Env [result] => some (env.get .here)) same)⟩

theorem denotePart_eq :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed (lower g)).denotePart evalOp input =
      (g.denote model (sourceInputs input)).map (fun value => Outcome.returned (.cons value .nil)) := by
  apply Part.ext
  intro outcome
  rw [Silmaril.MLIR.CF.SwitchAssert.Cfg.mem_denotePart_iff]
  simp only [Silmaril.MLIR.CF.SwitchAssert.Cfg.embed_run, Option.map_eq_some_iff]
  constructor
  · rintro ⟨fuel, output, run, rfl⟩
    cases output with
    | cons value rest =>
      cases rest
      exact Part.mem_map _ ((g.returns_iff_mem_denote model (sourceInputs input) value).mp
        ((returns_iff g input value).mpr ⟨fuel, run⟩))
  · intro observed
    obtain ⟨value, returned, rfl⟩ := (Part.mem_map_iff _).mp observed
    obtain ⟨fuel, run⟩ := (returns_iff g input value).mp
      ((g.returns_iff_mem_denote model (sourceInputs input) value).mpr returned)
    exact ⟨fuel, _, run, rfl⟩

end Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Proofs
