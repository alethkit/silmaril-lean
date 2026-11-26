module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.Thms
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Thms
meta import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.CaseExamples

open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction (Transfer region)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
  (Atom Denote PacketType PrimitiveSignature Program)
open Silmaril.Elgot.ITree (Tree Trace HasTrace ret vis iterate_fixpoint vis_bind hasTrace_vis_exchange_iff out_ret)
open Silmaril.Elgot.ITree.Finite (Event evaluate transition)

private def bit : PacketType := .coprod .unit .unit
private def replyType : PacketType := .coprod bit bit
private def sig : PrimitiveSignature Bool :=
  ⟨fun poll => if poll then .product bit bit else bit, fun poll => if poll then replyType else bit⟩
private abbrev Events := Event sig.Request sig.Reply

private def packets (_ : Fin 1) : PacketType := bit
private def exits (i : Fin 2) : PacketType := if i.val = 0 then .unit else .product bit bit

-- The second reply makes the selected row either revisit itself with
-- a new argument, or return the case payload paired with this visit's input.
private def polling : FiniteCFG Bool 1 2 1 where
  entry := .br 0 (.bv 0)
  block _ := .let₁ (.op false (.bv 0)) (.let₁ (.op true (.pair (.bv 1) (.bv 0)))
    (.case (.bv 0) (.br 0 (.bv 0)) (.br 2 (.pair (.bv 0) (.bv 3)))))

private def checked : Checked sig (.snoc .nil bit) packets exits polling :=
  (check sig (.snoc .nil bit) packets exits polling).get (by decide)

private def built :=
  (construct sig (fun i => (checked.shape.table i).1) exits checked.emitted.code).get (by decide)

example : checked.shape.row.requests = 2 := rfl
example : (checked.emitted.code.block 2).erase =
    .let₂ (.var 0) (.let₂ (.var 1)
      (.case (.var 2) (.br 0 (.var 0)) (.br 4 (.pair (.var 0) (.var 2))))) := rfl

-- A request inside a case leaf still falls outside the literal jump grammar.
example : (readRow sig packets exits [replyType] (.case (.var 0)
    (.let₁ (.op false (.var 0)) (.br 0 (.var 0))) (.br 2 (.pair (.var 0) (.var 0))))).isNone = true := rfl

private def dispatcher := built.program

private def primeKey (input : Denote bit) : sig.Request := ⟨false, input⟩
private def pollKey (input prime : Denote bit) : sig.Request := ⟨true, (input, prime)⟩

private def afterPrime (input prime : Denote bit) : dispatcher.State := by
  refine ⟨⟨.inl ⟨1, by decide⟩, ?_⟩⟩
  change Denote bit × Denote bit
  exact (input, prime)

private def afterPoll (input prime : Denote bit) (reply : Denote replyType) : dispatcher.State := by
  refine ⟨⟨.inl ⟨2, by decide⟩, ?_⟩⟩
  change (Denote bit × Denote bit) × Denote replyType
  exact ((input, prime), reply)

private def returned (payload input : Denote bit) : dispatcher.State := ⟨⟨.inr 1, (payload, input)⟩⟩

private theorem prime_step (input : Denote bit) :
    dispatcher.step (dispatcher.start 0 input) = .inl (.request (primeKey input) (afterPrime input)) := rfl

private theorem poll_step (input prime : Denote bit) :
    dispatcher.step (afterPrime input prime) = .inl (.request (pollKey input prime) (afterPoll input prime)) := rfl

private theorem repeat_step (input prime next : Denote bit) :
    dispatcher.step (afterPoll input prime (.inl next)) = .inr (dispatcher.start 0 next) := rfl

private theorem exit_step (input prime payload : Denote bit) :
    dispatcher.step (afterPoll input prime (.inr payload)) = .inr (returned payload input) := rfl

private theorem ret_eq_pure {A : Type 1} (value : A) : ret (E := Events) value = pure value := rfl

section Execution

variable {inputs : Fin 1 → PacketType} (program : Program sig inputs exits)

private noncomputable def runState (state : program.State) : Tree Events (Transfer Atom) :=
  evaluate program.step state >>= fun r => pure (FiniteCFG.packedTreeOutput (Program.renderResult r))

private theorem run_request {state : program.State} (key : sig.Request)
    (resume : sig.Reply key → program.State) (step : program.step state = .inl (.request key resume)) :
    runState program state = vis (.ask key) (fun reply => runState program (resume reply)) := by
  unfold runState evaluate
  rw [congrFun (iterate_fixpoint (transition program.step)) state]
  simp only [transition, step, vis_bind, ret_eq_pure, pure_bind, Sum.elim_inr]

private theorem run_jump {here next : program.State} (step : program.step here = .inr next) :
    runState program here = runState program next := by
  unfold runState evaluate
  rw [congrFun (iterate_fixpoint (transition program.step)) here]
  simp only [transition, step, ret_eq_pure, pure_bind, Sum.elim_inr]

private theorem run_result {state : program.State} {result : Program.Result exits}
    (step : program.step state = .inl (.result result)) :
    runState program state = pure (FiniteCFG.packedTreeOutput (Program.renderResult result)) := by
  unfold runState evaluate
  rw [congrFun (iterate_fixpoint (transition program.step)) state]
  simp only [transition, step, ret_eq_pure, pure_bind, Sum.elim_inl]

end Execution

private def output (payload input : Denote bit) : Transfer Atom :=
  FiniteCFG.packedTreeOutput (1, .pair (bit.encode payload) (bit.encode input))

private theorem run_exit (payload input : Denote bit) :
    runState dispatcher (returned payload input) = pure (output payload input) :=
  run_result dispatcher (result := ⟨⟨1, (payload, input)⟩⟩) rfl

private def env (input : Denote bit) : Env Atom := fun _ => bit.encode input

private theorem codec_id (value : Value Atom) : valueCodec id value = value := by
  induction value <;> simp_all only [valueCodec, id_eq]

private theorem primitivesAgree : PrimitivesAgree sig.primitive sig.primitive id := by
  intro op value
  rw [codec_id, show valueCodec (id : Atom → Atom) = id from funext codec_id, id_map]

private noncomputable def original {blocks : Nat} (graph : FiniteCFG Bool blocks 2 1)
    (input : Denote bit) : Tree Events (Transfer Atom) :=
  resultCodec id <$> (region sig.primitive (env input) graph.erase >>=
    fun out => pure (FiniteCFG.packedTreeOutput out))

private theorem source_packed (input : Denote bit) :
    original polling input = built.packed.observe (env input) (env input) :=
  checked.emitted.public_run built (env input) (env input) (env input) id primitivesAgree (codec_id _).symm

private theorem packed_state (input : Denote bit) :
    built.packed.observe (env input) (env input) = runState dispatcher (dispatcher.start 0 input) := by
  rw [built.packed.observe_eq input _ _ (fun _ => rfl)]
  change (dispatcher.observe 0 input >>= fun out => pure (FiniteCFG.packedTreeOutput out)) = _
  rw [dispatcher.observe_eq 0 input]
  simp only [runState, bind_assoc, pure_bind]

private def first : Denote bit := .inl ⟨⟩
private def second : Denote bit := .inr ⟨⟩

private def repeatThenExit : Trace Events (Transfer Atom) :=
  .exchange (.ask (primeKey first)) second
    (.exchange (.ask (pollKey first second)) (.inl second)
      (.exchange (.ask (primeKey second)) first
        (.exchange (.ask (pollKey second first)) (.inr first) (.result (output first second)))))

/-- Each visit completes both requests. The final reply selects the exit
and its payload survives alongside the second visit's input. -/
theorem repeat_then_exit :
    HasTrace (original polling first) repeatThenExit ∧
      HasTrace (built.packed.observe (env first) (env first)) repeatThenExit := by
  have trace : HasTrace (runState dispatcher (dispatcher.start 0 first)) repeatThenExit := by
    unfold repeatThenExit
    rw [run_request dispatcher _ _ (prime_step first)]
    erw [hasTrace_vis_exchange_iff]
    rw [run_request dispatcher _ _ (poll_step first second)]
    erw [hasTrace_vis_exchange_iff]
    rw [run_jump dispatcher (repeat_step first second second), run_request dispatcher _ _ (prime_step second)]
    erw [hasTrace_vis_exchange_iff]
    rw [run_request dispatcher _ _ (poll_step second first)]
    erw [hasTrace_vis_exchange_iff]
    rw [run_jump dispatcher (exit_step second first first), run_exit]
    exact out_ret _
  rw [source_packed, packed_state]
  exact ⟨trace, trace⟩

-- Both leaves stay within the old table. Block one receives only the
-- case payload and feeds it back. Block two receives the case payload
-- and the pre-request input, then returns that pair on the second exit.
private def internalPackets (i : Fin 3) : PacketType :=
  if i.val = 2 then .product bit bit else bit

private def internalPolling : FiniteCFG Bool 3 2 1 where
  entry := .br 0 (.bv 0)
  block i :=
    if i.val = 0 then .let₁ (.op true (.pair (.bv 0) (.bv 0)))
      (.case (.bv 0) (.br 1 (.bv 0)) (.br 2 (.pair (.bv 0) (.bv 2))))
    else if i.val = 1 then .br 0 (.bv 0)
    else .br 4 (.bv 0)

private def internalChecked : Checked sig (.snoc .nil bit) internalPackets exits internalPolling :=
  (check sig (.snoc .nil bit) internalPackets exits internalPolling).get (by decide)

private def internalBuilt :=
  (construct sig (fun i => (internalChecked.shape.table i).1) exits internalChecked.emitted.code).get (by decide)

private def internalDispatcher := internalBuilt.program

example : (internalBuilt.packed.target.block ((3 : Fin 4).cast internalBuilt.provenance.count)).erase =
    .let₂ (.var 0) (.case (.var 0) (.br 1 (.var 0)) (.br 2 (.pair (.var 0) (.var 2)))) :=
  (Constructed.row_erasure sig _ exits internalBuilt 3).symm.trans rfl

private def internalTail (input : Denote bit) (reply : Denote replyType) : internalDispatcher.State := by
  refine ⟨⟨.inl ⟨3, by decide⟩, ?_⟩⟩
  change Denote bit × Denote replyType
  exact (input, reply)

private def feedback (payload : Denote bit) : internalDispatcher.State := by
  refine ⟨⟨.inl ⟨1, by decide⟩, ?_⟩⟩
  exact payload

private def forward (payload input : Denote bit) : internalDispatcher.State := by
  refine ⟨⟨.inl ⟨2, by decide⟩, ?_⟩⟩
  change Denote bit × Denote bit
  exact (payload, input)

private def internalReturn (payload input : Denote bit) : internalDispatcher.State :=
  ⟨⟨.inr 1, (payload, input)⟩⟩

private theorem internal_request (input : Denote bit) :
    internalDispatcher.step (internalDispatcher.start 0 input) =
      .inl (.request (pollKey input input) (internalTail input)) := rfl

private theorem internal_left (input payload : Denote bit) :
    internalDispatcher.step (internalTail input (.inl payload)) = .inr (feedback payload) := rfl

private theorem internal_right (input payload : Denote bit) :
    internalDispatcher.step (internalTail input (.inr payload)) = .inr (forward payload input) := rfl

private theorem feedback_step (payload : Denote bit) :
    internalDispatcher.step (feedback payload) = .inr (internalDispatcher.start 0 payload) := rfl

private theorem forward_step (payload input : Denote bit) :
    internalDispatcher.step (forward payload input) = .inr (internalReturn payload input) := rfl

private theorem internal_source_packed (input : Denote bit) :
    original internalPolling input = internalBuilt.packed.observe (env input) (env input) :=
  internalChecked.emitted.public_run internalBuilt (env input) (env input) (env input) id primitivesAgree
    (codec_id _).symm

private theorem internal_packed_state (input : Denote bit) :
    internalBuilt.packed.observe (env input) (env input) =
      runState internalDispatcher (internalDispatcher.start 0 input) := by
  rw [internalBuilt.packed.observe_eq input _ _ (fun _ => rfl)]
  change (internalDispatcher.observe 0 input >>= fun out => pure (FiniteCFG.packedTreeOutput out)) = _
  rw [internalDispatcher.observe_eq 0 input]
  simp only [runState, bind_assoc, pure_bind]

private def internalTrace : Trace Events (Transfer Atom) :=
  .exchange (.ask (pollKey first first)) (.inl second)
    (.exchange (.ask (pollKey second second)) (.inr first) (.result (output first second)))

/-- The two internal jumps carry different packet types. The first
causes another visit and the second carries the distinct return fields. -/
theorem two_internal_leaves :
    HasTrace (original internalPolling first) internalTrace ∧
      HasTrace (internalBuilt.packed.observe (env first) (env first)) internalTrace := by
  have trace : HasTrace (runState internalDispatcher (internalDispatcher.start 0 first)) internalTrace := by
    unfold internalTrace
    rw [run_request internalDispatcher _ _ (internal_request first)]
    erw [hasTrace_vis_exchange_iff]
    rw [run_jump internalDispatcher (internal_left first second), run_jump internalDispatcher (feedback_step second),
      run_request internalDispatcher _ _ (internal_request second)]
    erw [hasTrace_vis_exchange_iff]
    rw [run_jump internalDispatcher (internal_right second first), run_jump internalDispatcher (forward_step first second),
      run_result internalDispatcher (result := ⟨⟨1, (first, second)⟩⟩) rfl]
    exact out_ret _
  rw [internal_source_packed, internal_packed_state]
  exact ⟨trace, trace⟩

private def outwardPolling : FiniteCFG Bool 1 2 1 where
  entry := .br 0 (.bv 0)
  block _ := .let₁ (.op true (.pair (.bv 0) (.bv 0)))
    (.case (.bv 0) (.br 1 .unit) (.br 2 (.pair (.bv 0) (.bv 2))))

private def outwardChecked : Checked sig (.snoc .nil bit) packets exits outwardPolling :=
  (check sig (.snoc .nil bit) packets exits outwardPolling).get (by decide)

example : (construct sig (fun i => (outwardChecked.shape.table i).1) exits
    outwardChecked.emitted.code).isSome = true := by decide

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.CaseExamples
