module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Defs
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Proofs

open Continuation.Partial
open Relation (ReflTransGen)

universe u v w z

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {primitives : Primitives m σ}

theorem get_capture {t : Ty V S} {context params : Ports (Ty V S)}
    (port : Port context t) (captures : Tuple m.Val context) (arguments : Tuple m.Val params) :
    (prependContext arguments captures).get (capturePort port) = captures.get port := by
  induction port with
  | head => cases captures; rfl
  | tail port ih => cases captures with | cons _ rest => exact ih rest

theorem project_related {context childContext : Ports (Ty V S)} {capL capR : Tuple m.Val context}
    (captured : TupleRelated m ids capL capR) (ports : Tuple (Port context) childContext) :
    TupleRelated m ids (projectCaptures capL ports) (projectCaptures capR ports) := by
  induction ports with
  | nil => exact .nil
  | cons port _ ih => exact .cons (captured.get port) ih

theorem read_projected {context params childContext childArgs : Ports (Ty V S)}
    {past : List (Ports (Ty V S))} (captures : Tuple m.Val context) (paramsIn : Tuple m.Val params)
    (locals : Locals m.Val past) (ports : Tuple (Port context) childContext)
    (arguments : Wires (context ++ params) past childArgs) :
    (captureInputs ports arguments).read
        (prependContext paramsIn captures) locals =
      prependContext (arguments.read (prependContext paramsIn captures) locals) (projectCaptures captures ports) := by
  induction ports with
  | nil => rfl
  | cons port rest ih =>
    exact congrArg₂ Tuple.cons (get_capture port captures paramsIn) ih


private theorem map_map {Ty : Type u} {F : Ty → Type v} {G : Ty → Type w} {H : Ty → Type z}
    {ports : Ports Ty} (xs : Tuple F ports) (f : ∀ t, F t → G t) (g : ∀ t, G t → H t) :
    (xs.map f).map g = xs.map (fun t x => g t (f t x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (Tuple.cons (g _ (f _ x))) ih

private theorem project_identity {context : Ports (Ty V S)} (caps : Tuple m.Val context) :
    projectCaptures caps (NestedTheta.identityPorts context) = caps := by
  induction caps with
  | nil => rfl
  | cons x xs ih =>
    unfold projectCaptures at ih ⊢
    simp only [NestedTheta.identityPorts, Tuple.map, Tuple.get, map_map]
    exact congrArg (Tuple.cons x) ih

private def keepsCaptures {context params : Ports (Ty V S)} (caps : Tuple m.Val context) :
    Continuation.Partial.Outcome m σ (Theta.BodyResults (context ++ params)) → Prop
  | .returned value _ => ∃ (tag : m.Val (.control 2)) (next : Tuple m.Val params),
      value = .cons tag (prependContext next caps)
  | .blocked .. => True

private theorem ret_outcome {args outs : Ports (Ty V S)} {past : List (Ports (Ty V S))}
    {wires : Wires args past outs} {input : Tuple m.Val args} {locals : Locals m.Val past} {store : σ}
    {outcome : Continuation.Partial.Outcome m σ outs}
    (ran : Eval primitives (.region (.ret wires) input locals) store outcome) :
    outcome = .returned (wires.read input locals) store := by
  cases ran
  rfl

private theorem bind_outcome {args outs head : Ports (Ty V S)} {past tail : List (Ports (Ty V S))}
    {node : NestedTheta.Node (Instruction Op) args past head} {children : Bodies node.kind node.childSigs}
    {rest : NestedTheta.Term (Instruction Op) args (past ++ [head]) tail outs}
    {input : Tuple m.Val args} {locals : Locals m.Val past} {store : σ}
    {outcome : Continuation.Partial.Outcome m σ outs}
    (ran : Eval primitives (.region (.bind node children rest) input locals) store outcome) :
    (∃ value middle, Eval primitives (.region rest input (locals.snoc value)) middle outcome) ∨
      ∃ (site : Site m) (pending : Continuation.Descent.Pending m site.outs outs) (stopped : σ),
        outcome = .blocked site pending stopped := by
  cases ran with
  | bind _ more => exact .inl ⟨_, _, more⟩
  | bindBlocked => exact .inr ⟨_, _, _, rfl⟩

private theorem returned_captures {context params : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}
    {body : NestedTheta.Term (Instruction Op) (context ++ params) past sigs (Theta.BodyResults (context ++ params))}
    {outcome : Continuation.Partial.Outcome m σ (Theta.BodyResults (context ++ params))} {locals : Locals m.Val past} {store : σ}
    (fixed : PreservesLoopCaptures Op context params body) (caps : Tuple m.Val context) (input : Tuple m.Val params)
    (ran : Eval primitives (.region body (prependContext input caps) locals) store outcome) :
    keepsCaptures caps outcome := by
  induction fixed generalizing store with
  | ret selector outputs =>
    rw [ret_outcome ran]
    unfold keepsCaptures
    refine ⟨(Wires.read (.cons selector .nil) (prependContext input caps) locals).get .head,
      outputs.read (prependContext input caps) locals, ?_⟩
    have read := read_projected caps input locals (NestedTheta.identityPorts context) outputs
    rw [project_identity] at read
    exact congrArg (Tuple.cons _) read
  | bind _ ih =>
    rcases bind_outcome ran with ⟨_, _, more⟩ | ⟨_, _, _, rfl⟩
    · exact ih more
    · trivial

/-- Once the initial carry contains the static capture prefix, every
completed feedback preserves those exact values in the same order. -/
theorem feedback_captures {context params : Ports (Ty V S)} {sigs : List (Ports (Ty V S))}
    {body : LoopBody Op (context ++ params) sigs} {first current : Tuple m.Val (context ++ params) × σ}
    (fixed : PreservesLoopCaptures Op context params body) (caps : Tuple m.Val context)
    (initial : ∃ input, first.1 = prependContext input caps)
    (completed : ReflTransGen (Feedback.Iteration primitives body) first current) :
    ∃ input, current.1 = prependContext input caps := by
  induction completed with
  | refl => exact initial
  | tail _ step ih =>
    obtain ⟨input, same⟩ := ih
    obtain ⟨_, ran, _⟩ := step
    rw [same] at ran
    obtain ⟨_, next, carried⟩ := returned_captures fixed caps input ran
    exact ⟨next, congrArg (fun | .cons _ carry => carry) carried⟩

theorem related_arguments {context params : Ports (Ty V S)} {capsL capsR : Tuple m.Val context}
    {inputL inputR : Tuple m.Val params}
    (related : TupleRelated m ids (prependContext inputL capsL) (prependContext inputR capsR)) :
    TupleRelated m ids inputL inputR := by
  induction context with
  | nil => cases capsL; cases capsR; exact related
  | cons _ _ ih =>
    cases capsL
    cases capsR
    cases related with
    | cons _ more => exact ih more

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Proofs
