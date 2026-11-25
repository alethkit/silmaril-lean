module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Defs

/-! Ordered partial linking along typed ω renumberings. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism

open Continuation.Partial (Primitives Site)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}

/-- Partial primitive actions agree on definedness. In the defined case
they produce related tuples and exactly the same new store. -/
inductive ActionRelated (m : Machine.{u, v, w} Op) (ids : GlobalRel) (σ : Type (max u v w))
    (ports : Ports (Ty V S)) :
    _root_.Part (Tuple m.Val ports × σ) → _root_.Part (Tuple m.Val ports × σ) → Prop where
  | undefined : ActionRelated m ids σ ports .none .none
  | returned {left right : Tuple m.Val ports} (paired : TupleRelated m ids left right) (store : σ) :
    ActionRelated m ids σ ports (.some (left, store)) (.some (right, store))

def ActionsRespect (primitives : Primitives m σ) (ids : GlobalRel) : Prop :=
  ∀ {ins outs : Ports (Ty V S)} (opcode : Op ins outs) {left right : Tuple m.Val ins},
    TupleRelated m ids left right → ∀ store,
      ActionRelated m ids σ outs ((primitives.step opcode left).run store) ((primitives.step opcode right).run store)

/-- A diagnostic keeps the same typed opcode and relates every operand
in order. The initializer's internal numbering is fixed in this slice. -/
inductive SitesRelated (m : Machine.{u, v, w} Op) (ids : GlobalRel) : Site m → Site m → Prop where
  | same {left : Site m} {input : Tuple m.Val left.ins} (paired : TupleRelated m ids left.input input) :
    SitesRelated m ids left {left with input := input}

inductive OutcomesRelated (m : Machine.{u, v, w} Op) (ids : GlobalRel) (σ : Type (max u v w))
    (rename : Nat → Nat) (ports : Ports (Ty V S)) :
    Outcome m σ ports → Outcome m σ ports → Prop where
  | linked {left right : Tuple m.Val ports} (exports : TupleRelated m ids left right) (store : σ) :
    OutcomesRelated m ids σ rename ports (.linked left store) (.linked right store)
  | undefined {unitL unitR vertexL vertexR : Nat} {siteL siteR : Site m}
      (position : rename vertexL = vertexR) (identity : ids (unitL, vertexL) (unitR, vertexR))
      (site : SitesRelated m ids siteL siteR) (store : σ) :
    OutcomesRelated m ids σ rename ports
      (.undefined ⟨unitL, vertexL, siteL, store⟩) (.undefined ⟨unitR, vertexR, siteR, store⟩)

variable {args outs : Ports (Ty V S)} {pastL pastR : List (Ports (Ty V S))}

/-- The only vertices that may be passed independently in the two
linearizations are closed φ declarations with no members or outputs. -/
def emptyPhi (Op : Dialect.{u, v} (ValueSort V S) S) (args : Ports (Ty V S))
    (past : List (Ports (Ty V S))) : PhiTerm Op args past [] :=
  ⟨[], .nil, .nil⟩

/-- Pair captures by typed addresses. The executed code of a δ is shared
verbatim, so its primitive order and all γ arm positions are fixed. -/
inductive Binding (Op : Dialect.{u, v} (ValueSort V S) S) (rename : Nat → Nat) (args : Ports (Ty V S))
    (pastL pastR : List (Ports (Ty V S))) :
    {ports : Ports (Ty V S)} → VertexTerm Op args pastL ports → VertexTerm Op args pastR ports → Prop where
  | lambda {fn : Function V S} {left : LambdaTerm Op args pastL fn} {right : LambdaTerm Op args pastR fn}
      (paired : left.Renumbered rename right) : Binding Op rename args pastL pastR (.lambda left) (.lambda right)
  | delta {value : ValueSort V S} {context : Ports (Ty V S)} {sigs : List (Ports (Ty V S))}
      {left : Wires args pastL context} {right : Wires args pastR context}
      (captures : CaptureRenumbered rename left right)
      (initializer : Term Op context [] sigs [.value value]) :
    Binding Op rename args pastL pastR (.delta ⟨context, left, sigs, initializer⟩)
      (.delta ⟨context, right, sigs, initializer⟩)

/-- Match the ordered bindings at their mapped absolute positions, with
only empty φ declarations allowed to occur at different points. The outer
graph isomorphism independently checks the full vertex bijection. -/
inductive Ordered (Op : Dialect.{u, v} (ValueSort V S) S) (rename : Nat → Nat) (args outs : Ports (Ty V S)) :
    {pastL pastR sigsL sigsR : List (Ports (Ty V S))} →
    ModuleTerm Op args pastL sigsL outs → ModuleTerm Op args pastR sigsR outs → Prop where
  | ret {pastL pastR : List (Ports (Ty V S))} (left : Wires args pastL outs) (right : Wires args pastR outs) :
    Ordered Op rename args outs (.ret left) (.ret right)
  | bind {pastL pastR sigsL sigsR : List (Ports (Ty V S))} {head : Ports (Ty V S)}
      {left : VertexTerm Op args pastL head} {right : VertexTerm Op args pastR head}
      {restL : ModuleTerm Op args (pastL ++ [head]) sigsL outs}
      {restR : ModuleTerm Op args (pastR ++ [head]) sigsR outs}
      (position : rename pastL.length = pastR.length) (paired : Binding Op rename args pastL pastR left right)
      (rest : Ordered Op rename args outs restL restR) :
    Ordered Op rename args outs (.bind left restL) (.bind right restR)
  | emptyLeft {pastL pastR sigsL sigsR : List (Ports (Ty V S))}
      {restL : ModuleTerm Op args (pastL ++ [[]]) sigsL outs} {right : ModuleTerm Op args pastR sigsR outs}
      (rest : Ordered Op rename args outs restL right) :
    Ordered Op rename args outs (.bind (.phi (emptyPhi Op args pastL)) restL) right
  | emptyRight {pastL pastR sigsL sigsR : List (Ports (Ty V S))}
      {left : ModuleTerm Op args pastL sigsL outs} {restR : ModuleTerm Op args (pastR ++ [[]]) sigsR outs}
      (rest : Ordered Op rename args outs left restR) :
    Ordered Op rename args outs left (.bind (.phi (emptyPhi Op args pastR)) restR)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism
