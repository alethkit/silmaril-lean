module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Wiring.Thms

/-! Scheduled weak steps of the real partial continuation machine. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall

open Continuation (Stack)
open Continuation.Partial (Config Primitives Step)
open Relation (TransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {args ins outs final : Ports (Ty V S)}

abbrev Code (Op : Dialect.{u, v} (ValueSort V S) S) :=
  NestedTheta.Term (Instruction Op)

abbrev simple {past : List (Ports (Ty V S))} (instruction : Instruction Op ins outs)
    (wires : Wires args past ins) (cs : Fin 0 → List (Ports (Ty V S))) :
    NestedTheta.Node (Instruction Op) args past outs :=
  ⟨ins, .base (.simple instruction), wires, cs⟩

abbrev emptyGamma {past : List (Ports (Ty V S))} {entry : Ports (Ty V S)} {extra : Nat}
    (wires : Wires args past (.control (extra + 2) :: entry)) :
    NestedTheta.Node (Instruction Op) args past [] :=
  ⟨_, .base (.gamma extra), wires, fun _ => []⟩

/-- Align each primitive and application in execution order, checking
typed wire endpoints and the actual binding addresses. Only a γ whose
arms immediately return the empty tuple can move independently. -/
inductive Schedule (Op : Dialect.{u, v} (ValueSort V S) S) (vertices : Nat ≃ Nat) :
    {args outs : Ports (Ty V S)} → {pastL pastR sigsL sigsR : List (Ports (Ty V S))} →
    Code Op args pastL sigsL outs → Code Op args pastR sigsR outs → Prop where
  | ret {args outs : Ports (Ty V S)} {pastL pastR : List (Ports (Ty V S))}
      (left : Wires args pastL outs) (right : Wires args pastR outs)
      (edges : left.addresses.map (Address.rename vertices) = right.addresses) :
      Schedule Op vertices (.ret left) (.ret right)
  | bind {args outs ins head : Ports (Ty V S)}
      {pastL pastR sigsL sigsR : List (Ports (Ty V S))}
      (instruction : Instruction Op ins head)
      (left : Wires args pastL ins) (right : Wires args pastR ins)
      {csL csR : Fin 0 → List (Ports (Ty V S))}
      {childrenL : (i : Fin 0) → Code Op [] [] (csL i) []}
      {childrenR : (i : Fin 0) → Code Op [] [] (csR i) []}
      {restL : Code Op args (pastL ++ [head]) sigsL outs}
      {restR : Code Op args (pastR ++ [head]) sigsR outs}
      (position : vertices pastL.length = pastR.length)
      (edges : left.addresses.map (Address.rename vertices) = right.addresses)
      (rest : Schedule Op vertices restL restR) :
      Schedule Op vertices (.bind (simple instruction left csL) childrenL restL)
        (.bind (simple instruction right csR) childrenR restR)
  | emptyLeft {args outs entry : Ports (Ty V S)}
      {pastL pastR sigsL sigsR : List (Ports (Ty V S))} {extra : Nat}
      (wires : Wires args pastL (.control (extra + 2) :: entry))
      {restL : Code Op args (pastL ++ [[]]) sigsL outs} {right : Code Op args pastR sigsR outs}
      (rest : Schedule Op vertices restL right) :
      Schedule Op vertices (.bind (emptyGamma wires) (fun _ => .ret .nil) restL) right
  | emptyRight {args outs entry : Ports (Ty V S)}
      {pastL pastR sigsL sigsR : List (Ports (Ty V S))} {extra : Nat}
      (wires : Wires args pastR (.control (extra + 2) :: entry))
      {left : Code Op args pastL sigsL outs} {restR : Code Op args (pastR ++ [[]]) sigsR outs}
      (rest : Schedule Op vertices left restR) :
      Schedule Op vertices left (.bind (emptyGamma wires) (fun _ => .ret .nil) restR)

/-- The order check is on the real resolved bodies. The common typed
capture boundary allows the actual arguments to be appended on entry. -/
inductive ResolvedSchedule (Op : Dialect.{u, v} (ValueSort V S) S) (m : Machine.{u, v, w} Op)
    (fn : Function V S) : Closure Op m.Val fn → Closure Op m.Val fn → Prop where
  | intro {context : Ports (Ty V S)} {left right : Tuple m.Val context}
      {sigsL sigsR : List (Ports (Ty V S))}
      {bodyL : NestedTheta.Graph (Instruction Op) (context ++ fn.args) [] sigsL fn.results}
      {bodyR : NestedTheta.Graph (Instruction Op) (context ++ fn.args) [] sigsR fn.results}
      {vertices : Nat ≃ Nat} (code : Schedule Op vertices bodyL.toTerm bodyR.toTerm) :
      ResolvedSchedule Op m fn ⟨context, left, sigsL, bodyL⟩ ⟨context, right, sigsR, bodyR⟩

/-- Both frames suspend their actual suffix, entry and locals. The
paired producer position is that of the binding waiting for a result. -/
inductive Frames (m : Machine.{u, v, w} Op) (ids : GlobalRel) (final : Ports (Ty V S)) :
    {ports : Ports (Ty V S)} → Stack m ports final → Stack m ports final → Prop where
  | halt : Frames m ids final .halt .halt
  | resume {args head outs : Ports (Ty V S)} {pastL pastR sigsL sigsR : List (Ports (Ty V S))}
      {vertices : Nat ≃ Nat}
      {restL : Code Op args (pastL ++ [head]) sigsL outs}
      {restR : Code Op args (pastR ++ [head]) sigsR outs}
      {entryL entryR : Tuple m.Val args} {localsL : Locals m.Val pastL} {localsR : Locals m.Val pastR}
      {outerL outerR : Stack m outs final}
      (position : vertices pastL.length = pastR.length)
      (suffix : Schedule Op vertices restL restR)
      (entry : TupleRelated m ids entryL entryR)
      (locals : LocalsRelated m ids vertices localsL localsR)
      (outer : Frames m ids final outerL outerR) :
      Frames m ids final (.resume restL entryL localsL outerL) (.resume restR entryR localsR outerR)

/-- Boundaries of the scheduled partial machine. Inside an administrative
γ the machines can be at different controls, so only its endpoints are
related. Invocation and return retain the original typed stacks. -/
inductive Live (m : Machine.{u, v, w} Op) (ids : GlobalRel) (σ : Type (max u v w))
    (final : Ports (Ty V S)) : Config m σ final → Config m σ final → Prop where
  | region {args outs : Ports (Ty V S)} {pastL pastR sigsL sigsR : List (Ports (Ty V S))}
      {vertices : Nat ≃ Nat}
      {left : Code Op args pastL sigsL outs} {right : Code Op args pastR sigsR outs}
      {entryL entryR : Tuple m.Val args} {localsL : Locals m.Val pastL} {localsR : Locals m.Val pastR}
      {stackL stackR : Stack m outs final} (store : σ)
      (schedule : Schedule Op vertices left right)
      (entry : TupleRelated m ids entryL entryR)
      (locals : LocalsRelated m ids vertices localsL localsR)
      (frames : Frames m ids final stackL stackR) :
      Live m ids σ final ⟨.eval (.region left entryL localsL) stackL, store⟩
        ⟨.eval (.region right entryR localsR) stackR, store⟩
  | instruction {ins outs : Ports (Ty V S)} {stackL stackR : Stack m outs final}
      {inputL inputR : Tuple m.Val ins} (store : σ) (opcode : Instruction Op ins outs)
      (csL csR : Fin 0 → List (Ports (Ty V S)))
      (childrenL : (i : Fin 0) → Code Op [] [] (csL i) [])
      (childrenR : (i : Fin 0) → Code Op [] [] (csR i) [])
      (inputs : TupleRelated m ids inputL inputR) (frames : Frames m ids final stackL stackR) :
      Live m ids σ final ⟨.eval (.node (.base (.simple opcode)) csL childrenL inputL) stackL, store⟩
        ⟨.eval (.node (.base (.simple opcode)) csR childrenR inputR) stackR, store⟩
  | call {args outs : Ports (Ty V S)} {calleeL calleeR : m.Val (.value (.function args outs))}
      {inputL inputR : Tuple m.Val args} {stackL stackR : Stack m outs final} (store : σ)
      (callees : ValueRelated m ids calleeL calleeR) (inputs : TupleRelated m ids inputL inputR)
      (frames : Frames m ids final stackL stackR) :
      Live m ids σ final ⟨.eval (.call calleeL inputL) stackL, store⟩
        ⟨.eval (.call calleeR inputR) stackR, store⟩
  | returned {outs : Ports (Ty V S)} {valueL valueR : Tuple m.Val outs}
      {stackL stackR : Stack m outs final} (store : σ)
      (values : TupleRelated m ids valueL valueR) (frames : Frames m ids final stackL stackR) :
      Live m ids σ final ⟨.returned valueL stackL, store⟩ ⟨.returned valueR stackR, store⟩

/-- A local admission condition checked only at the active call boundary.
It constrains the syntax returned by the resolver and requires no call rank. -/
def DispatchReady (left right : Config m σ final) : Prop :=
  ∀ {args outs : Ports (Ty V S)} {calleeL calleeR : m.Val (.value (.function args outs))}
    {inputL inputR : Tuple m.Val args} {stackL stackR : Stack m outs final},
    left.control = .eval (.call calleeL inputL) stackL →
    right.control = .eval (.call calleeR inputR) stackR →
    ResolvedSchedule Op m ⟨args, outs⟩ (resolve m calleeL) (resolve m calleeR)

/-- Both machines reach another boundary by positive paths, or agree on
the exact kind of terminal observation. A block exposes the actual typed
attempt and the entire mapped stack, including the binding that owns it. -/
inductive Advance (primitives : Primitives m σ) (ids : GlobalRel)
    (left right : Config m σ final) : Prop where
  | stepped {nextL nextR : Config m σ final}
      (pathL : TransGen (Step primitives) left nextL) (pathR : TransGen (Step primitives) right nextR)
      (paired : Live m ids σ final nextL nextR) : Advance primitives ids left right
  | returned {valueL valueR : Tuple m.Val final} {store : σ}
      (values : TupleRelated m ids valueL valueR)
      (resultL : left.result = some (valueL, store)) (resultR : right.result = some (valueR, store)) :
      Advance primitives ids left right
  | blocked {ins outs : Ports (Ty V S)} (opcode : Op ins outs)
      {inputL inputR : Tuple m.Val ins} (inputs : TupleRelated m ids inputL inputR)
      {csL csR : Fin 0 → List (Ports (Ty V S))}
      {childrenL : (i : Fin 0) → Code Op [] [] (csL i) []}
      {childrenR : (i : Fin 0) → Code Op [] [] (csR i) []}
      {stackL stackR : Stack m outs final} (frames : Frames m ids final stackL stackR)
      (siteL : Continuation.Partial.selectedPrimitive left.control =
        some ⟨⟨ins, outs, opcode, csL, childrenL, inputL⟩, stackL⟩)
      (siteR : Continuation.Partial.selectedPrimitive right.control =
        some ⟨⟨ins, outs, opcode, csR, childrenR, inputR⟩, stackR⟩)
      (sameStore : left.store = right.store)
      (undefinedL : (primitives.step opcode inputL).run left.store = _root_.Part.none)
      (undefinedR : (primitives.step opcode inputR).run right.store = _root_.Part.none) :
      Advance primitives ids left right

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall
