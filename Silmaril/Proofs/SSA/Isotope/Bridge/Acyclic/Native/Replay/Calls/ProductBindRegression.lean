module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.ProductBind.Thms
import Silmaril.SSA.Isotope.LetCase.Structural.Reply.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.ConstructorJoin.Thms

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native.ProductBind

open LetCase.Structural.Finite (Shape)
open LetCase.Structural.Reply (run)
open LetSeq.StraightLine.Structural (Event Log Trace model)
open Isotope.Semantics (BoundEnv)
open Silmaril.Semantics.NondeterministicTrace.Finite (mem_bind)
open Region.Paper.WithComputedCallReturns
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

private inductive Op where
  | prepare
  | produce
  | consume
  | right

private abbrev bit : Shape := .sum .unit .unit
private abbrev rightField : Shape := .pair .unit bit
private abbrev X := bit.ty
private abbrev Y := rightField.ty
private abbrev P := Ty.product X Y
private abbrev β : BoundCtx (Ty Empty) 1 := .snoc .nil X
private abbrev γ := (β.snoc X).snoc Y

private instance : LetCase.Structural.Finite.Signature Op where
  source
    | .consume => .pair bit (.pair rightField bit)
    | _ => bit
  target
    | .produce => .pair bit rightField
    | .right => rightField
    | _ => bit

private def producer : Operand Op β P :=
  ⟨.op .produce (.op .prepare (.bv 0)), .op (.op .bv)⟩

private def pairProducer : Operand Op β P :=
  ⟨.pair (.op .prepare (.bv 0)) (.op .right (.bv 0)), .pair (.op .bv) (.op .bv)⟩

private def consume : Operand Op γ X :=
  ⟨.op .consume (.pair (.bv 1) (.pair (.bv 0) (.bv 2))), .op (.pair .bv (.pair .bv .bv))⟩

private def written (p : Operand Op β P) : Code Op β X :=
  .let₂ p (.let₁ consume (.br ⟨.bv 0, .bv⟩))

private abbrev exits : LCtx (Ty Empty) := [X, X]
private theorem second : At exits 1 X := rfl

-- The two exit payload types coincide. Both checked equations still use
-- exit one at the written and reified native endpoints.
example : ∃ s, Schedule [X] s exits [.prepare, .produce, .consume] ∧
    Eqv false [X] ((written producer).toSSA 1) s exits ∧
    Eqv false [X] ((Code.ofLetCase (.let₂ producer.2 consume.2)).guardedSSA 1) s exits :=
  operand_schedule second producer consume trivial ⟨trivial, trivial, trivial⟩

example : ∃ s, Schedule [X] s exits [.prepare, .right, .consume] ∧
    Eqv false [X] ((written pairProducer).toSSA 1) s exits ∧
    Eqv false [X] ((Code.ofLetCase (.let₂ pairProducer.2 consume.2)).guardedSSA 1) s exits :=
  operand_schedule second pairProducer consume ⟨trivial, trivial⟩ ⟨trivial, trivial, trivial⟩

private def scheduledProducer : Region Op :=
  .let₁ (.op .prepare (.var 0)) (.let₁ (.op .produce (.var 0)) (.br 0 (.var 0)))

private def scheduled : Region Op :=
  .let₁ (.op .prepare (.var 0)) (.let₁ (.op .produce (.var 0))
    (.let₂ (.var 0)
      (.let₁ (.op .consume (.pair (.var 1) (.pair (.var 0) (.var 4))))
        (.br 1 (.var 0)))))

private def consumer : Region Op := (.br consume : Code Op γ X).guardedSSA 1

-- The exact scheduled region keeps the left field at one, the right at
-- zero, and the original capture below the producer's two fresh replies.
example : Schedule [X] scheduled exits [.prepare, .produce, .consume] ∧
    Eqv false [X] ((written producer).toSSA 1) scheduled exits := by
  have runProducer : CallSchedule [X] scheduledProducer P [.prepare, .produce] :=
    .call (.var rfl) (.call (.var rfl) (.ret (.var rfl)))
  have step := Step.seq Op.produce (.op (.var (i := 0) rfl) : Tm.HasType [X] (.op Op.prepare (.var 0)) X)
  have ep : Eqv false [X] ((Code.br producer).guardedSSA 0) scheduledProducer [P] :=
    .extra step.valueBranches.1.hasType step.valueBranches.2.hasType (.inl (.inl (.inr step)))
  have ec : Schedule [Y, X, X] consumer exits [.consume] :=
    .call (.pair (.var (i := 1) rfl) (.pair (.var (i := 0) rfl) (.var (i := 2) rfl)))
      (.ret second (.var rfl))
  exact ⟨.call (.var rfl) (.call (.var rfl) (.unpackVar (i := 0) rfl
      (.call (.pair (.var (i := 1) rfl) (.pair (.var (i := 0) rfl) (.var (i := 4) rfl)))
        (.ret second (.var rfl))))),
    bind_replay (.op (.op (.var rfl))) runProducer.valueBranches ep
      (Region.Paper.Extension.Eqv.refl ec.valueBranches.hasType)⟩

private abbrev V := LetSeq.StraightLine.Structural.Value (α := Empty)
private abbrev eval := (model (α := Empty) (Φ := Op)).eval

-- In the concrete observation the original input is the argument of
-- prepare, while consume sees the two produced fields and that same input.
-- The monadic expression has one occurrence of each reached request.
private theorem run_written (ρ : BoundEnv V β) :
    run (written producer).toLetCase.2 ρ =
      ((eval .prepare (ρ 0) >>= eval .produce) >>= fun ab =>
        eval .consume (ab.1, (ab.2, ρ 0))) := by
  change (((((pure (ρ 0) : Trace Empty Op (V X)) >>= eval .prepare) >>= eval .produce) >>=
    fun ab => ((do
      let l ← (pure ab.1 : Trace Empty Op (V X))
      let rest ← (do
        let r ← (pure ab.2 : Trace Empty Op (V Y))
        let x ← (pure (ρ 0) : Trace Empty Op (V X))
        pure (r, x) : Trace Empty Op (V (Ty.product Y X)))
      pure (l, rest) : Trace Empty Op (V (instrSrc Op.consume))) >>= eval .consume) >>= pure)) = _
  have pure_step {A B : Type} (x : A) (k : A → Trace Empty Op B) :
      ((pure x : Trace Empty Op A) >>= k) = k x := pure_bind _ _
  simp only [pure_step, bind_assoc, bind_pure]
  rw [show ((pure (ρ 0) : Trace Empty Op (V X)) >>= eval .prepare) =
    eval .prepare (ρ 0) from pure_bind _ _]
  congr 1
  funext ab
  exact (pure_step (A := V X) (B := V X) (ρ 0) _).trans
    ((pure_step (A := V (Ty.product Y X)) (B := V X) (ab.2, ρ 0) _).trans
      (pure_step (ab.1, (ab.2, ρ 0)) (eval .consume)))

example (ρ : BoundEnv V β) {result : V X} {log : Log Empty Op}
    (observed : (result, log) ∈ (run (written producer).toLetCase.2 ρ).outcomes) :
    log.toList.map Event.generator = [.prepare, .produce, .consume] := by
  have sequence :
      ((eval .prepare (ρ 0) >>= eval .produce) >>= fun ab => eval .consume (ab.1, (ab.2, ρ 0))) =
        (eval .prepare (ρ 0) >>= fun prepared =>
          eval .produce prepared >>= fun ab => eval .consume (ab.1, (ab.2, ρ 0))) :=
    bind_assoc _ _ _
  rw [run_written, sequence] at observed
  obtain ⟨_, _, _, ⟨_, prepareEvent⟩, afterPrepare, rfl⟩ := mem_bind.mp observed
  obtain ⟨_, _, _, ⟨_, produceEvent⟩, afterProduce, rfl⟩ := mem_bind.mp afterPrepare
  obtain ⟨_, consumeEvent⟩ := afterProduce
  rw [← (Prod.mk.inj prepareEvent).2, ← (Prod.mk.inj produceEvent).2, ← (Prod.mk.inj consumeEvent).2]
  rfl

end Silmaril.Isotope.LambdaSSA.Acyclic.Native.ProductBind
