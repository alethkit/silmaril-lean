module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Invocation.Defs

/-! Observation transport for exported λ closures with shared acyclic or single-θ code. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Invocation

open Continuation.Partial (Primitives Site Config Step)
open Continuation.Descent (Pending)
open PartialLink.Invocation (Request)
open Relation (ReflTransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {args outs carried : Ports (Ty V S)} {sigs : List (Ports (Ty V S))}

/-- A single θ vertex whose inputs are explicit argument wires. -/
abbrev loopVertex (initial : Wires args [] carried) (sigs : List (Ports (Ty V S))) :
    NestedTheta.Node (Instruction Op) args [] carried :=
  ⟨carried, .theta carried, initial, fun _ => sigs⟩

/-- The common numbered λ body has acyclic primitive/γ code, or one θ
with such a body and a result wiring suffix. All executed primitive
orders are fixed within a region. -/
inductive SharedCode (Op : Dialect.{u, v} (ValueSort V S) S) (args outs : Ports (Ty V S)) :
    {sigs : List (Ports (Ty V S))} → NestedTheta.Term (Instruction Op) args [] sigs outs → Prop where
  | acyclic {sigs : List (Ports (Ty V S))} (term : Term Op args [] sigs outs) :
    SharedCode Op args outs (embed term)
  | theta {carried : Ports (Ty V S)} {sigs : List (Ports (Ty V S))}
      (initial : Wires args [] carried) (body : Term Op carried [] sigs (Theta.BodyResults carried))
      (results : Wires args [carried] outs) :
    SharedCode Op args outs (.bind (loopVertex initial sigs) (fun _ => embed body) (.ret results))

variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {params results : Ports (Ty V S)}

/-- Both selected values are real λ closures with the same admitted
body. Their captures can differ, as recorded by the runtime value relation. -/
inductive SharedLambda (m : Machine.{u, v, w} Op) (params results : Ports (Ty V S)) :
    m.Val (.value (.function params results)) → m.Val (.value (.function params results)) → Prop where
  | closure {context : Ports (Ty V S)} {sigs : List (Ports (Ty V S))}
      {left right : Tuple m.Val context}
      {body : NestedTheta.Term (Instruction Op) (context ++ params) [] sigs results}
      (shared : SharedCode Op (context ++ params) results body) :
    SharedLambda m params results (.closure left body.toGraph) (.closure right body.toGraph)

def request (unitId : Nat) (graph : Omega Op args outs sigs) (imports : Tuple m.Val args)
    (port : Port outs (.value (.function params results))) (arguments : Tuple m.Val params) (store : σ) :
    Request m σ results :=
  ⟨unitId, args, outs, sigs, graph, imports, params, port, arguments, store⟩

/-- Paired observations of actual partial dispatch. Invocation cases use
actual machine paths from the precise post-link configurations. -/
inductive ObservationsRelated (primitives : Primitives m σ) (ids : GlobalRel) (rename : Nat → Nat)
    (results : Ports (Ty V S)) :
    Except (Failure m σ) (Config m σ results) → Except (Failure m σ) (Config m σ results) → Prop where
  | linkBlocked {unitL unitR vertexL vertexR : Nat} {siteL siteR : Site m}
      (address : rename vertexL = vertexR) (identity : ids (unitL, vertexL) (unitR, vertexR))
      (site : SitesRelated m ids siteL siteR) (store : σ) :
    ObservationsRelated primitives ids rename results
      (.error ⟨unitL, vertexL, siteL, store⟩) (.error ⟨unitR, vertexR, siteR, store⟩)
  | returned {sourceL sourceR : Config m σ results} {valueL valueR : Tuple m.Val results} {store : σ}
      (values : TupleRelated m ids valueL valueR)
      (left : ReflTransGen (Step primitives) sourceL ⟨.returned valueL .halt, store⟩)
      (right : ReflTransGen (Step primitives) sourceR ⟨.returned valueR .halt, store⟩) :
    ObservationsRelated primitives ids rename results (.ok sourceL) (.ok sourceR)
  | invocationBlocked {sourceL sourceR : Config m σ results} {siteL siteR : Site m}
      {pendingL : Pending m siteL.outs results} {pendingR : Pending m siteR.outs results} {store : σ}
      (site : SitesRelated m ids siteL siteR)
      (left : ReflTransGen (Step primitives) sourceL ⟨.eval siteL.job (pendingL.push .halt), store⟩)
      (right : ReflTransGen (Step primitives) sourceR ⟨.eval siteR.job (pendingR.push .halt), store⟩)
      (blockedL : (Config.mk (.eval siteL.job (pendingL.push .halt)) store).Blocked primitives)
      (blockedR : (Config.mk (.eval siteR.job (pendingR.push .halt)) store).Blocked primitives) :
    ObservationsRelated primitives ids rename results (.ok sourceL) (.ok sourceR)
  | diverges {sourceL sourceR : Config m σ results}
      (left : InfiniteTrace (Step primitives) sourceL) (right : InfiniteTrace (Step primitives) sourceR) :
    ObservationsRelated primitives ids rename results (.ok sourceL) (.ok sourceR)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Invocation
