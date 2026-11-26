module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Thms

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Proofs

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg WordOp emitOpsWithResults emitOpWithResults model registerWithResults)
open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow Val read)
open Silmaril.SSA.RVSDG (Locals Origin Port Tuple Wires extend)

variable {arity : Nat} {past sigs : List (List PortTy)}

private def LocalsMatch (arity : Nat) (fr : Frame Reg) (base : Nat) :
    {past : List (List PortTy)} → Locals (Val model.value) past → Prop
  | [], _ => True
  | _ :: _, xs =>
    (∀ port : Port _ wordPort, fr.get (resultReg arity base) = some (xs.1.get port)) ∧
      LocalsMatch arity fr (base + 1) xs.2

private theorem locals_read (xs : Locals (Val model.value) past) {fr : Frame Reg} {base : Nat}
    (matched : LocalsMatch arity fr base xs) (i : Fin past.length) (port : Port past[i] wordPort) :
    fr.get (resultReg arity (base + i.val)) = some ((xs.get i).get port) := by
  induction past generalizing base with
  | nil => exact i.elim0
  | cons head tail ih =>
    cases i using Fin.cases with
    | zero => exact matched.1 port
    | succ i =>
      change fr.get (resultReg arity (base + i.succ.val)) = some ((xs.2.get i).get port)
      simpa only [Fin.val_succ, Nat.add_succ, Nat.succ_add] using ih xs.2 matched.2 i port

private theorem read_origin (input : WordTuple arity) (xs : Locals (Val model.value) past) (fr : Frame Reg)
    (args : ArgsMatch fr input) (matched : LocalsMatch arity fr 0 xs)
    (wire : Origin (wordPorts arity) past wordPort) :
    fr.get (entryReg arity wire.address) = some (read model wire input xs) := by
  cases wire with
  | arg port => exact args port
  | output i port =>
    change fr.get (resultReg arity i.val) = some ((xs.get i).get port)
    simpa only [Nat.zero_add] using locals_read xs matched i port

private theorem append_local (xs : Locals (Val model.value) past) {fr : Frame Reg} {base : Nat}
    (value : Word) (matched : LocalsMatch arity fr base xs) :
    LocalsMatch arity (fr.set (resultReg arity (base + past.length)) value) base
      (xs.snoc (Tuple.cons (F := Val model.value) (t := wordPort) value .nil)) := by
  induction past generalizing base with
  | nil =>
    constructor
    · intro port
      cases port with
      | head => simp [Locals.snoc]; rfl
      | tail impossible => nomatch impossible
    · exact trivial
  | cons head tail ih =>
    constructor
    · intro port
      have fresh : resultReg arity base ≠ resultReg arity (base + (head :: tail).length) := by
        unfold resultReg
        intro same
        have := Reg.arg.inj same
        simp only [List.length_cons] at this
        omega
      simpa only [Locals.snoc, Frame.get_set, ite_eq_right fresh] using matched.1 port
    · have index : base + (head :: tail).length = base + 1 + tail.length := by
        simp only [List.length_cons]
        omega
      rw [index]
      exact ih xs.2 matched.2

private theorem index_lt {ports : List PortTy} {t : PortTy} (port : Port ports t) :
    port.index < ports.length := by
  induction port with
  | head => simp [Port.index]
  | tail _ ih => simpa [Port.index] using Nat.succ_lt_succ ih

private theorem preserve_args (input : WordTuple arity) (fr : Frame Reg) (args : ArgsMatch fr input)
    (index : Nat) (value : Word) : ArgsMatch (fr.set (resultReg arity index) value) input := by
  intro port
  have bound : port.index < arity := by simpa [wordPorts, wordSorts] using index_lt port
  simpa [resultReg, show port.index ≠ arity + arity + index by omega] using args port

private theorem resolved (wire : Origin (wordPorts arity) past wordPort) :
    registerWithResults (fun port => .arg port.index) (resultReg arity) wire =
      entryReg arity wire.address := by
  cases wire <;> rfl

private theorem arithmetic_exec (input : WordTuple arity) (xs : Locals (Val model.value) past) (fr : Frame Reg)
    (mem : Memory) (args : ArgsMatch fr input) (matched : LocalsMatch arity fr 0 xs)
    (op : FeedbackOp) (operands : Wires (wordPorts arity) past [wordPort, wordPort]) :
    (emitOpWithResults (fun port => .arg port.index) (resultReg arity) (resultReg arity past.length)
      op.source operands).exec fr mem =
      some (fr.set (resultReg arity past.length) (model.run op.source (operands.read input xs)), mem) := by
  cases operands with
  | cons left rest =>
    cases rest with
    | cons right tail =>
      cases tail
      cases op <;> simp only [FeedbackOp.source, emitOpWithResults, Tuple.get, resolved,
        Op.exec, read_origin input xs fr args matched] <;> rfl

private theorem table_steps (flow : Dataflow WordOp (wordPorts arity) past sigs)
    (prog : Prog Reg) (block : Block Reg) (found : prog.block? 0 0 = some block)
    (input : WordTuple arity) (mem : Memory)
    (ok : supported flow = true) (prefixOps : List (Op Reg)) (size : prefixOps.length = past.length)
    (code : block.ops = prefixOps ++ emit flow)
    (fr : Frame Reg) (xs : Locals (Val model.value) past) (args : ArgsMatch fr input)
    (matched : LocalsMatch arity fr 0 xs) :
    ∃ ready,
      StepsNWithin prog [] sigs.length ⟨⟨0, 0, past.length⟩, fr, [], mem⟩
        ⟨⟨0, 0, past.length + sigs.length⟩, ready, [], mem⟩ ∧
      ArgsMatch ready input ∧ LocalsMatch arity ready 0 (flow.eval model input xs) := by
  induction flow generalizing fr prefixOps with
  | nil => exact ⟨fr, .refl, args, matched⟩
  | @cons past sigs sorts out op operands rest ih =>
    cases op <;> simp only [supported, Bool.false_eq_true] at ok
    case' add => let operation := FeedbackOp.add
    case' sub => let operation := FeedbackOp.sub
    all_goals
      let instruction := emitOpWithResults (fun port => .arg port.index) (resultReg arity)
        (resultReg arity past.length) operation.source operands
      have emitted : block.ops = prefixOps ++ instruction :: emit rest := code
      have fetched : prog.fetch ⟨0, 0, past.length⟩ = some (.op instruction) := by
        simp [Prog.fetch, found, emitted, size]
      have remainder : block.ops = (prefixOps ++ [instruction]) ++ emit rest := by
        rw [emitted, List.append_assoc]
        rfl
      let value := model.run operation.source (operands.read input xs)
      have execute := Transition.op (s := (⟨⟨0, 0, past.length⟩, fr, [], mem⟩ : State Reg))
        fetched (arithmetic_exec input xs fr mem args matched operation operands)
      have saved : LocalsMatch arity (fr.set (resultReg arity past.length) value) 0
          (xs.snoc (Tuple.cons (F := Val model.value) (t := wordPort) value .nil)) := by
        simpa only [Nat.zero_add] using append_local (base := 0) xs value matched
      obtain ⟨ready, steps, captures, locals⟩ := ih ok (prefixOps ++ [instruction]) (by simp [size])
        remainder (fr.set (resultReg arity past.length) value)
        (xs.snoc (Tuple.cons (F := Val model.value) (t := wordPort) value .nil))
        (preserve_args input fr args past.length value) saved
      simp only [List.length_append, List.length_singleton] at steps
      refine ⟨ready, ?_, captures, locals⟩
      simp only [List.length_cons]
      rw [show past.length + (sigs.length + 1) = past.length + 1 + sigs.length by omega]
      exact .head ⟨execute.step_eq, List.nil_suffix⟩ steps

theorem entry_block (flow : Dataflow WordOp (wordPorts arity) [] sigs)
    (prog : Prog Reg) (block : Block Reg) (found : prog.block? 0 0 = some block)
    (input : WordTuple arity) (mem : Memory) (ok : supported flow = true)
    (ops : block.ops = emit flow) (fr : Frame Reg) (args : ArgsMatch fr input) :
    ∃ ready, StepsNWithin prog [] sigs.length ⟨⟨0, 0, 0⟩, fr, [], mem⟩
      ⟨⟨0, 0, sigs.length⟩, ready, [], mem⟩ ∧ ArgsMatch ready input ∧
      ∀ wire : Origin (wordPorts arity) (extend [] sigs) wordPort,
        ready.get (entryReg arity wire.address) =
          some (read model wire input (flow.eval model input PUnit.unit)) := by
  obtain ⟨ready, steps, captures, locals⟩ :=
    table_steps flow prog block found input mem ok [] rfl ops fr PUnit.unit args trivial
  exact ⟨ready, by simpa only [List.length_nil, Nat.zero_add] using steps, captures,
    read_origin input _ ready captures locals⟩

theorem emit_length (flow : Dataflow WordOp (wordPorts arity) past sigs) :
    (emit flow).length = sigs.length := by
  induction flow with
  | nil => rfl
  | cons _ _ _ ih => simp only [emit, emitOpsWithResults, List.length_cons] at ih ⊢; rw [ih]

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Proofs
