module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Machine

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Proofs

open Relation (ReflTransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ports final : Ports (Ty V S)}
variable {primitives : Primitives m σ} {job : Job m ports} {store : σ} {outcome : Outcome m σ ports}

private def validates (outcome : Outcome m σ ports) (frame : Stack m ports final) : Prop :=
  match outcome with
  | .returned .. => True
  | .blocked .. => (outcome.atStack frame).Blocked primitives

private theorem eval_sound (evaluation : Eval primitives job store outcome) (frame : Stack m ports final) :
    ReflTransGen (Step primitives) ⟨.eval job frame, store⟩ (outcome.atStack frame) ∧
      validates (primitives := primitives) outcome frame := by
  induction evaluation with
  | call _ ih =>
    obtain ⟨steps, valid⟩ := ih frame
    exact ⟨steps.head (pure_step rfl), valid⟩
  | ret => exact ⟨.single (pure_step rfl), trivial⟩
  | @bind args head ports past tail node children rest entry locals store middle value outcome first more ihFirst ihMore =>
    let saved := Stack.resume rest entry locals frame
    have entered : Step primitives ⟨.eval (.region (.bind node children rest) entry locals) frame, store⟩
        ⟨.eval (.node node.kind node.childSigs children (node.inputs.read entry locals)) saved, store⟩ :=
      pure_step rfl
    have resumed : Step primitives ⟨.returned value saved, middle⟩
        ⟨.eval (.region rest entry (locals.snoc value)) frame, middle⟩ :=
      pure_step rfl
    obtain ⟨steps, valid⟩ := ihMore frame
    exact ⟨(((ihFirst saved).1.head entered).tail resumed).trans steps, valid⟩
  | @bindBlocked args head ports past tail node children rest entry locals store stopped site pending first ih =>
    obtain ⟨steps, valid⟩ := ih (.resume rest entry locals frame)
    exact ⟨steps.head (pure_step rfl), valid⟩
  | @primitive site store finalStore value defined =>
    refine ⟨.single ?_, trivial⟩
    change (Config.mk (.returned value frame) finalStore) ∈ (Config.mk (.eval site.job frame) store).next primitives
    exact _root_.Part.mem_map (fun (output, nextStore) => Config.mk (.returned output frame) nextStore) defined
  | primitiveBlocked site store undefined =>
    exact ⟨.refl, ⟨⟨site, frame⟩, rfl, undefined⟩⟩
  | apply _ ih =>
    obtain ⟨steps, valid⟩ := ih frame
    exact ⟨steps.head (pure_step rfl), valid⟩
  | gamma _ ih =>
    obtain ⟨steps, valid⟩ := ih frame
    exact ⟨steps.head (pure_step rfl), valid⟩
  | theta _ ih =>
    obtain ⟨steps, valid⟩ := ih frame
    exact ⟨steps.head (pure_step rfl), valid⟩
  | @stop carried sigs body input output tag store finalStore activation done ih =>
    have entered : Step primitives ⟨.eval (.iteration body input) frame, store⟩
        ⟨.eval (.region body input PUnit.unit) (.loop body frame), store⟩ := pure_step rfl
    have exited : Step primitives ⟨.returned (.cons tag output) (.loop body frame), finalStore⟩
        ⟨.returned output frame, finalStore⟩ := by
      apply pure_step
      change _root_.Part.some (Config.mk (State.finishLoop body tag output frame) finalStore) =
        _root_.Part.some (Config.mk (.returned output frame) finalStore)
      simp only [State.finishLoop, done, Bool.false_eq_true, ↓reduceIte]
    exact ⟨((ih (.loop body frame)).1.head entered).tail exited, trivial⟩
  | @again carried sigs body input next tag store middle outcome activation feedback later ihFirst ihLater =>
    have entered : Step primitives ⟨.eval (.iteration body input) frame, store⟩
        ⟨.eval (.region body input PUnit.unit) (.loop body frame), store⟩ := pure_step rfl
    have restarted : Step primitives ⟨.returned (.cons tag next) (.loop body frame), middle⟩
        ⟨.eval (.iteration body next) frame, middle⟩ := by
      apply pure_step
      change _root_.Part.some (Config.mk (State.finishLoop body tag next frame) middle) =
        _root_.Part.some (Config.mk (.eval (.iteration body next) frame) middle)
      rw [State.finishLoop, ite_eq_left feedback]
    obtain ⟨steps, valid⟩ := ihLater frame
    exact ⟨(((ihFirst (.loop body frame)).1.head entered).tail restarted).trans steps, valid⟩
  | @loopBlocked carried sigs body input store stopped site pending activation ih =>
    obtain ⟨steps, valid⟩ := ih (.loop body frame)
    exact ⟨steps.head (pure_step rfl), valid⟩

theorem eval_steps (evaluation : Eval primitives job store outcome) (frame : Stack m ports final) :
    ReflTransGen (Step primitives) ⟨.eval job frame, store⟩ (outcome.atStack frame) :=
  (eval_sound evaluation frame).1

theorem eval_blocked {site : Site m} {pending : Descent.Pending m site.outs ports} {stopped : σ}
    (evaluation : Eval primitives job store (.blocked site pending stopped)) (frame : Stack m ports final) :
    (Config.mk (.eval site.job (pending.push frame)) stopped).Blocked primitives :=
  (eval_sound evaluation frame).2

private theorem of_total_returns {value : Tuple m.Val ports} (returned : Recursive.Returns m job value) (store : σ) :
    Eval (Primitives.liftTotal m σ) job store (.returned value store) := by
  induction returned with
  | call _ ih => exact .call ih
  | ret wires entry locals => exact .ret wires entry locals store
  | bind _ _ first more => exact .bind first more
  | primitive opcode cs children input =>
    exact .primitive ⟨_, _, opcode, cs, children, input⟩ (_root_.Part.mem_some _)
  | apply _ ih => exact .apply ih
  | gamma _ ih => exact .gamma ih
  | theta _ ih => exact .theta ih
  | stop _ done ih => exact .stop ih done
  | again _ feedback _ first more => exact .again first feedback more

private theorem path_liftTotal_store {source target : Config m σ final}
    (path : ReflTransGen (Step (Primitives.liftTotal m σ)) source target) :
    source.store = target.store := by
  induction path with
  | refl => rfl
  | tail _ step ih => exact ih.trans (step_liftTotal.mp step).2

theorem eval_liftTotal {value : Tuple m.Val ports} {finalStore : σ} :
    Eval (Primitives.liftTotal m σ) job store (.returned value finalStore) ↔
      Recursive.Returns m job value ∧ store = finalStore := by
  constructor
  · intro evaluated
    have path := eval_steps evaluated (Stack.halt : Stack m ports ports)
    have plain : Continuation.Completes (start job) value :=
      ReflTransGen.lift Config.control (fun _ _ edge => (step_liftTotal.mp edge).1) _ _ path
    exact ⟨completes_sound plain, path_liftTotal_store path⟩
  · rintro ⟨returned, rfl⟩
    exact of_total_returns returned store

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Proofs
