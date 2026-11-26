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

-- The selected case requires mixed destinations and literal jump leaves.
example : (readRow sig packets exits [replyType] (.case (.var 0) (.br 0 (.var 0)) (.br 0 (.var 0)))).isNone = true :=
  rfl

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

private noncomputable def runState (state : dispatcher.State) : Tree Events (Transfer Atom) :=
  evaluate dispatcher.step state >>= fun r => pure (FiniteCFG.packedTreeOutput (Program.renderResult r))

private theorem run_request {state : dispatcher.State} (key : sig.Request)
    (resume : sig.Reply key → dispatcher.State) (step : dispatcher.step state = .inl (.request key resume)) :
    runState state = vis (.ask key) (fun reply => runState (resume reply)) := by
  unfold runState evaluate
  rw [congrFun (iterate_fixpoint (transition dispatcher.step)) state]
  simp only [transition, step, vis_bind, ret_eq_pure, pure_bind, Sum.elim_inr]

private theorem run_jump {here next : dispatcher.State} (step : dispatcher.step here = .inr next) :
    runState here = runState next := by
  unfold runState evaluate
  rw [congrFun (iterate_fixpoint (transition dispatcher.step)) here]
  simp only [transition, step, ret_eq_pure, pure_bind, Sum.elim_inr]

private def output (payload input : Denote bit) : Transfer Atom :=
  FiniteCFG.packedTreeOutput (1, .pair (bit.encode payload) (bit.encode input))

private theorem run_exit (payload input : Denote bit) :
    runState (returned payload input) = pure (output payload input) := by
  unfold runState evaluate
  rw [congrFun (iterate_fixpoint (transition dispatcher.step)) (returned payload input)]
  have step : dispatcher.step (returned payload input) = .inl (.result ⟨⟨1, (payload, input)⟩⟩) := rfl
  simp only [transition, step, ret_eq_pure, pure_bind, Sum.elim_inl]
  rfl

private def env (input : Denote bit) : Env Atom := fun _ => bit.encode input

private theorem codec_id (value : Value Atom) : valueCodec id value = value := by
  induction value <;> simp_all only [valueCodec, id_eq]

private theorem primitivesAgree : PrimitivesAgree sig.primitive sig.primitive id := by
  intro op value
  rw [codec_id, show valueCodec (id : Atom → Atom) = id from funext codec_id, id_map]

private noncomputable def original (input : Denote bit) : Tree Events (Transfer Atom) :=
  resultCodec id <$> (region sig.primitive (env input) polling.erase >>=
    fun out => pure (FiniteCFG.packedTreeOutput out))

private theorem source_packed (input : Denote bit) :
    original input = built.packed.observe (env input) (env input) :=
  checked.emitted.public_run built (env input) (env input) (env input) id primitivesAgree (codec_id _).symm

private theorem packed_state (input : Denote bit) :
    built.packed.observe (env input) (env input) = runState (dispatcher.start 0 input) := by
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
    HasTrace (original first) repeatThenExit ∧
      HasTrace (built.packed.observe (env first) (env first)) repeatThenExit := by
  have trace : HasTrace (runState (dispatcher.start 0 first)) repeatThenExit := by
    unfold repeatThenExit
    rw [run_request _ _ (prime_step first)]
    erw [hasTrace_vis_exchange_iff]
    rw [run_request _ _ (poll_step first second)]
    erw [hasTrace_vis_exchange_iff]
    rw [run_jump (repeat_step first second second), run_request _ _ (prime_step second)]
    erw [hasTrace_vis_exchange_iff]
    rw [run_request _ _ (poll_step second first)]
    erw [hasTrace_vis_exchange_iff]
    rw [run_jump (exit_step second first first), run_exit]
    exact out_ret _
  rw [source_packed, packed_state]
  exact ⟨trace, trace⟩

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.CaseExamples
