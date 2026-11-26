module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Proofs

open Continuation (Stack State)
open Continuation.Partial (Config Primitives Step selectedPrimitive)
open Relation (ReflTransGen TransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {args outs final : Ports (Ty V S)} {pastL pastR sigsL sigsR : List (Ports (Ty V S))}
variable {primitives : Primitives m σ}

private theorem structural {left : Config m σ final} {right : State m final}
    (shape : selectedPrimitive left.control = none) (next : left.control.next = some right) :
    Step primitives left ⟨right, left.store⟩ :=
  Step.of_next_some (by simp only [Config.next, shape, next, Option.map_some, _root_.Part.ofOption])

private theorem skip_empty {past sigs : List (Ports (Ty V S))} {entry : Ports (Ty V S)} {extra : Nat}
    (wires : Wires args past (.control (extra + 2) :: entry))
    (rest : Code Op args (past ++ [[]]) sigs outs)
    (input : Tuple m.Val args) (locals : Locals m.Val past) (stack : Stack m outs final) (store : σ) :
    ReflTransGen (Step primitives)
      ⟨.eval (.region (.bind (emptyGamma wires) (fun _ => .ret .nil) rest) input locals) stack, store⟩
      ⟨.eval (.region rest input (locals.snoc .nil)) stack, store⟩ := by
  let frame := Stack.resume rest input locals stack
  let child := fun _ : Fin (extra + 2) => (.ret .nil : Code Op entry [] [] [])
  let kind := NestedTheta.Kind.base (Shape.gamma (Op := Instruction Op) (entry := entry) (exit := []) extra)
  have enter : Step primitives
      ⟨.eval (.region (.bind (emptyGamma wires) child rest) input locals) stack, store⟩
      ⟨.eval (.node kind (fun _ => []) child (wires.read input locals)) frame, store⟩ :=
    structural rfl rfl
  generalize wires.read input locals = chosen at enter
  cases chosen with
  | cons tag payload =>
    have select : Step primitives ⟨.eval (.node kind (fun _ => []) child (.cons tag payload)) frame, store⟩
        ⟨.eval (.region (past := []) (.ret .nil) payload PUnit.unit) frame, store⟩ := structural rfl rfl
    have returned : Step primitives ⟨.eval (.region (past := []) (.ret .nil) payload PUnit.unit) frame, store⟩
        ⟨.returned .nil frame, store⟩ := structural rfl rfl
    have resume : Step primitives ⟨.returned .nil frame, store⟩
        ⟨.eval (.region rest input (locals.snoc .nil)) stack, store⟩ := structural rfl rfl
    exact (((ReflTransGen.single enter).tail select).tail returned).tail resume

private theorem region_progress {vertices : Nat ≃ Nat}
    {left : Code Op args pastL sigsL outs} {right : Code Op args pastR sigsR outs}
    (schedule : Schedule Op vertices left right)
    {entryL entryR : Tuple m.Val args} (entry : TupleRelated m ids entryL entryR)
    {localsL : Locals m.Val pastL} {localsR : Locals m.Val pastR}
    (locals : LocalsRelated m ids vertices localsL localsR)
    {stackL stackR : Stack m outs final} (frames : Frames m ids final stackL stackR) (store : σ) :
    ∃ nextL nextR,
      TransGen (Step primitives) ⟨.eval (.region left entryL localsL) stackL, store⟩ nextL ∧
      TransGen (Step primitives) ⟨.eval (.region right entryR localsR) stackR, store⟩ nextR ∧
      Live m ids σ final nextL nextR := by
  induction schedule with
  | ret left right edges =>
    exact ⟨_, _, .single (structural rfl rfl), .single (structural rfl rfl),
      .returned store (readWires_related entry locals left right edges) frames⟩
  | bind instruction left right position edges suffix _ =>
    exact ⟨_, _, .single (structural rfl rfl), .single (structural rfl rfl),
      .instruction store instruction _ _ _ _ (readWires_related entry locals left right edges)
        (.resume position suffix entry locals frames)⟩
  | gamma left right position edges children suffix _ _ =>
    exact ⟨_, _, .single (structural rfl rfl), .single (structural rfl rfl),
      .gamma store children (readWires_related entry locals left right edges)
        (.resume position suffix entry locals frames)⟩
  | theta left right position edges body suffix _ _ =>
    exact ⟨_, _, .single (structural rfl rfl), .single (structural rfl rfl),
      .theta store body (readWires_related entry locals left right edges)
        (.resume position suffix entry locals frames)⟩
  | emptyLeft wires suffix ih =>
    obtain ⟨nextL, nextR, pathL, pathR, related⟩ := ih entry locals.emptyLeft frames
    exact ⟨nextL, nextR, TransGen.trans_right (skip_empty wires _ _ _ _ _) pathL, pathR, related⟩
  | emptyRight wires suffix ih =>
    obtain ⟨nextL, nextR, pathL, pathR, related⟩ := ih entry locals.emptyRight frames
    exact ⟨nextL, nextR, pathL, TransGen.trans_right (skip_empty wires _ _ _ _ _) pathR, related⟩

private theorem prepend_related {context : Ports (Ty V S)} {left right : Tuple m.Val context}
    {inputL inputR : Tuple m.Val args} (inputs : TupleRelated m ids inputL inputR)
    (captures : TupleRelated m ids left right) :
    TupleRelated m ids (prependContext inputL left) (prependContext inputR right) := by
  induction context with
  | nil => cases captures; exact inputs
  | cons _ _ ih =>
    cases captures with
    | cons head tail => exact .cons head (ih tail)

theorem open_related {calleeL calleeR : m.Val (.value (.function args outs))}
    {inputL inputR : Tuple m.Val args} {stackL stackR : Stack m outs final}
    (callees : ValueRelated m ids calleeL calleeR)
    (inputs : TupleRelated m ids inputL inputR)
    (code : ResolvedSchedule Op m ⟨args, outs⟩ (resolve m calleeL) (resolve m calleeR))
    (frames : Frames m ids final stackL stackR) (store : σ) :
    Live m ids σ final ⟨.eval (Job.openClosure m calleeL inputL) stackL, store⟩
      ⟨.eval (Job.openClosure m calleeR inputR) stackR, store⟩ := by
  have captures := (Recursive.resolve_related callees).1
  unfold Job.openClosure
  generalize resolve m calleeL = left at code captures ⊢
  generalize resolve m calleeR = right at code captures ⊢
  cases code with
  | intro schedule =>
    exact .region store schedule (prepend_related inputs captures) LocalsRelated.empty frames

private theorem primitive_step {ins outs : Ports (Ty V S)} (opcode : Op ins outs)
    (cs : Fin 0 → List (Ports (Ty V S))) (children : (i : Fin 0) → Code Op [] [] (cs i) [])
    (input : Tuple m.Val ins) (stack : Stack m outs final) (store : σ)
    {value : Tuple m.Val outs} {middle : σ}
    (ran : (primitives.step opcode input).run store = _root_.Part.some (value, middle)) :
    Step primitives ⟨.eval (.node (.base (.simple (.primitive opcode))) cs children input) stack, store⟩
      ⟨.returned value stack, middle⟩ := by
  apply Step.of_next_some
  change ((primitives.step opcode input).run store).map _ = _
  rw [ran]
  rfl

theorem advance {left right : Config m σ final}
    (actions : ActionsRespect primitives ids) (pair : Live m ids σ final left right)
    (ready : DispatchReady left right) : Advance primitives ids left right := by
  cases pair with
  | region store schedule entry locals frames =>
    obtain ⟨_, _, pathL, pathR, related⟩ := region_progress (primitives := primitives) schedule entry locals frames store
    exact .stepped pathL pathR related
  | @call args outs calleeL calleeR inputL inputR stackL stackR store callees inputs frames =>
    exact .stepped (.single (structural rfl rfl)) (.single (structural rfl rfl))
      (open_related callees inputs (ready rfl rfl) frames store)
  | returned store values frames =>
    cases frames with
    | halt => exact .returned values rfl rfl
    | @resume args head outs pastL pastR sigsL sigsR vertices restL restR entryL entryR localsL localsR
        outerL outerR position suffix entry locals outer =>
      exact .stepped (.single (structural rfl rfl)) (.single (structural rfl rfl))
        (.region store suffix entry (locals.snoc vertices.injective position values) outer)
    | loop body outer =>
      cases values with
      | cons selector carried =>
        cases selector with
        | control tag =>
          by_cases again : (tag.val == 1) = true
          · refine .stepped (.single (structural rfl ?_)) (.single (structural rfl ?_))
              (.iteration store body carried outer) <;>
              simp only [State.next, State.finishLoop, Colour.selector, ite_eq_left again]
          · refine .stepped (.single (structural rfl ?_)) (.single (structural rfl ?_))
              (.returned store carried outer) <;>
              simp only [State.next, State.finishLoop, Colour.selector, ite_eq_right again]
  | theta store body inputs frames =>
    exact .stepped (.single (structural rfl rfl)) (.single (structural rfl rfl))
      (.iteration store body inputs frames)
  | iteration store body inputs frames =>
    exact .stepped (.single (structural rfl rfl)) (.single (structural rfl rfl))
      (.region store body inputs LocalsRelated.empty (.loop body frames))
  | gamma store children inputs frames =>
    cases inputs with
    | cons selector captures =>
      cases selector with
      | control tag =>
        exact .stepped (.single (structural rfl rfl)) (.single (structural rfl rfl))
          (.region store (children tag) captures LocalsRelated.empty frames)
  | @instruction ins outs stackL stackR inputL inputR store opcode csL csR childL childR inputs frames =>
    cases opcode with
    | apply fn =>
      cases inputs with
      | cons callees arguments =>
        exact .stepped (.single (structural rfl rfl)) (.single (structural rfl rfl))
          (.call store callees arguments frames)
    | primitive opcode =>
      have related := actions opcode inputs store
      generalize ranL : (primitives.step opcode inputL).run store = actionL at related
      generalize ranR : (primitives.step opcode inputR).run store = actionR at related
      cases related with
      | undefined => exact .blocked opcode inputs frames rfl rfl rfl ranL ranR
      | returned results middle =>
        exact .stepped (.single (primitive_step opcode csL childL inputL stackL store ranL))
          (.single (primitive_step opcode csR childR inputR stackR store ranR)) (.returned middle results frames)

private theorem result_no_step {source next : Config m σ final}
    {value : Tuple m.Val final} {store : σ} (returned : source.result = some (value, store)) :
    ¬ Step primitives source next := by
  obtain ⟨control, initial⟩ := source
  cases control with
  | eval => simp [Config.result, State.result] at returned
  | returned values stack =>
    cases stack with
    | halt => exact _root_.Part.notMem_none _
    | resume => simp [Config.result, State.result] at returned
    | loop => simp [Config.result, State.result] at returned

private theorem after_first {a b c : Config m σ final} (first : Step primitives a b)
    (path : TransGen (Step primitives) a c) : ReflTransGen (Step primitives) b c := by
  obtain ⟨next, step, rest⟩ := TransGen.head'_iff.mp path
  exact (_root_.Part.mem_unique step first) ▸ rest

theorem advance_steps {left right : Config m σ final}
    (progress : Advance primitives ids left right) :
    (∀ firstL, Step primitives left firstL → ∃ nextL nextR,
      ReflTransGen (Step primitives) firstL nextL ∧ TransGen (Step primitives) right nextR ∧
      Live m ids σ final nextL nextR) ∧
    (∀ firstR, Step primitives right firstR → ∃ nextL nextR,
      TransGen (Step primitives) left nextL ∧ ReflTransGen (Step primitives) firstR nextR ∧
      Live m ids σ final nextL nextR) := by
  cases progress with
  | stepped pathL pathR paired =>
    exact ⟨fun _ first => ⟨_, _, after_first first pathL, pathR, paired⟩,
      fun _ first => ⟨_, _, pathL, after_first first pathR, paired⟩⟩
  | returned _ resultL resultR =>
    exact ⟨fun _ first => (result_no_step resultL first).elim,
      fun _ first => (result_no_step resultR first).elim⟩
  | blocked _ _ _ siteL siteR _ undefinedL undefinedR =>
    have blockedL : left.Blocked primitives := ⟨_, siteL, undefinedL⟩
    have blockedR : right.Blocked primitives := ⟨_, siteR, undefinedR⟩
    exact ⟨fun _ first => (blockedL.no_step first).elim,
      fun _ first => (blockedR.no_step first).elim⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Proofs
