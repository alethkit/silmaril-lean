module

public import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Initializers
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Thms
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Thms
public import Silmaril.SSA.RVSDG.Interprocedural.Isomorphism.Thms
public import Silmaril.SSA.RVSDG.Thms
import Mathlib.Data.Fin.Embedding

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Proofs

open Continuation.Partial (Primitives Eval)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {primitives : Primitives m σ} {unitL unitR : Nat} {rename : Nat → Nat}
variable {args head outs : Ports (Ty V S)}
variable {pastL pastR sigsL sigsR : List (Ports (Ty V S))}

private theorem open_delta {value : ValueSort V S} (delta : DeltaTerm Op args pastL value)
    (input : Tuple m.Val args) (locals : Locals m.Val pastL) :
    initializerJob delta.toGraph input locals =
      .region (embed delta.initializer) (delta.captures.read input locals) PUnit.unit := by
  simp only [initializerJob, DeltaTerm.toGraph, Term.toTerm_toGraph]

private theorem binding_related (respects : ActionsRespect primitives ids)
    {left : VertexTerm Op args pastL head} {right : VertexTerm Op args pastR head}
    (binding : Binding Op rename args pastL pastR left right)
    (position : rename pastL.length = pastR.length)
    (identity : ids (unitL, pastL.length) (unitR, pastR.length))
    {inputL inputR : Tuple m.Val args} (inputs : TupleRelated m ids inputL inputR)
    {localsL : Locals m.Val pastL} {localsR : Locals m.Val pastR}
    (locals : LocalsRelated m ids rename localsL localsR) (store : σ) :
    ∃ outcomeL outcomeR,
      LinksVertex primitives unitL inputL localsL left.toGraph store outcomeL ∧
      LinksVertex primitives unitR inputR localsR right.toGraph store outcomeR ∧
      OutcomesRelated m ids σ rename head outcomeL outcomeR := by
  cases binding with
  | @lambda fn left right paired =>
    obtain ⟨contextL, capturesL, sigsL, bodyL⟩ := left
    obtain ⟨contextR, capturesR, sigsR, bodyR⟩ := right
    obtain ⟨⟨same, edges⟩, bodies⟩ := paired
    change contextL = contextR at same
    subst contextR
    have captures := read_related inputs locals capturesL capturesR edges
    exact ⟨_, _, rfl, rfl, .linked (.cons (.closure captures bodies) .nil) store⟩
  | @phi members left right paired =>
    obtain ⟨contextL, capturesL, definitionsL⟩ := left
    obtain ⟨contextR, capturesR, definitionsR⟩ := right
    obtain ⟨⟨same, edges⟩, definitions⟩ := paired
    change contextL = contextR at same
    subst contextR
    have captures := read_related inputs locals capturesL capturesR edges
    exact ⟨_, _, rfl, rfl, .linked (Recursive.phiMembers_related captures definitions) store⟩
  | @delta value context sigs capturesL capturesR captures initializer =>
    have related := read_related inputs locals capturesL capturesR captures.2
    obtain ⟨outcomeL, outcomeR, ranL, ranR, observations⟩ := initializer_related respects initializer
      related LocalsRelated.empty store
    have actualL : Eval primitives (initializerJob (DeltaTerm.toGraph ⟨context, capturesL, sigs, initializer⟩)
        inputL localsL) store outcomeL := by
      rw [open_delta]
      exact ranL
    have actualR : Eval primitives (initializerJob (DeltaTerm.toGraph ⟨context, capturesR, sigs, initializer⟩)
        inputR localsR) store outcomeR := by
      rw [open_delta]
      exact ranR
    cases observations with
    | returned outputs finalStore =>
      exact ⟨_, _, LinksDelta.linked actualL, LinksDelta.linked actualR,
        .linked (.cons (.global identity (outputs.get .head)) .nil) finalStore⟩
    | blocked sites stopped =>
      exact ⟨_, _, LinksDelta.undefined actualL, LinksDelta.undefined actualR,
        .undefined position identity sites stopped⟩

private theorem table_related (respects : ActionsRespect primitives ids)
    (injective : Function.Injective rename)
    (identities : ∀ i, ids (unitL, i) (unitR, rename i))
    {left : ModuleTerm Op args pastL sigsL outs} {right : ModuleTerm Op args pastR sigsR outs}
    (schedule : Ordered Op rename args outs left right)
    (exports : left.results.addresses.map (Address.rename rename) = right.results.addresses)
    {inputL inputR : Tuple m.Val args} (inputs : TupleRelated m ids inputL inputR)
    {localsL : Locals m.Val pastL} {localsR : Locals m.Val pastR}
    (locals : LocalsRelated m ids rename localsL localsR) (store : σ) :
    ∃ outcomeL outcomeR,
      LinksTable primitives unitL inputL outs localsL left.vertices left.results store outcomeL ∧
      LinksTable primitives unitR inputR outs localsR right.vertices right.results store outcomeR ∧
      OutcomesRelated m ids σ rename outs outcomeL outcomeR := by
  induction schedule generalizing store with
  | ret left right =>
    exact ⟨_, _, .ret _ _ _ _, .ret _ _ _ _, .linked (read_related inputs locals left right exports) store⟩
  | bind position paired _ ih =>
    have identity := position ▸ identities _
    obtain ⟨_, _, firstL, firstR, relation⟩ := binding_related respects paired position identity inputs locals store
    cases relation with
    | linked outputs middle =>
      obtain ⟨_, _, tailL, tailR, related⟩ := ih exports (locals.snoc injective position outputs) middle
      exact ⟨_, _, .bind firstL tailL, .bind firstR tailR, related⟩
    | undefined vertex identity sites store =>
      exact ⟨_, _, .stop firstL, .stop firstR, .undefined vertex identity sites store⟩
  | emptyLeft _ ih =>
    obtain ⟨_, _, tailL, tailR, related⟩ := ih exports locals.emptyLeft store
    exact ⟨_, _, .bind (values := (.nil : Tuple m.Val [])) (middle := store) rfl tailL, tailR, related⟩
  | emptyRight _ ih =>
    obtain ⟨_, _, tailL, tailR, related⟩ := ih exports locals.emptyRight store
    exact ⟨_, _, tailL, .bind (values := (.nil : Tuple m.Val [])) (middle := store) rfl tailR, related⟩

private theorem rename_injective {n k : Nat} (rename : Fin n ≃ Fin k) :
    Function.Injective (renameVertex rename) := by
  have same : n = k := Fin.equiv_iff_eq.mp ⟨rename⟩
  subst k
  intro x y equal
  unfold renameVertex at equal
  by_cases inL : x < n <;> by_cases inR : y < n
  · rw [dite_eq_left inL, dite_eq_left inR] at equal
    exact congrArg Fin.val (rename.injective (Fin.ext equal))
  · rw [dite_eq_left inL, dite_eq_right inR] at equal
    exact False.elim (inR (equal ▸ (rename ⟨x, inL⟩).isLt))
  · rw [dite_eq_right inL, dite_eq_left inR] at equal
    exact False.elim (inL (equal.symm ▸ (rename ⟨y, inR⟩).isLt))
  · rwa [dite_eq_right inL, dite_eq_right inR] at equal

theorem link_related (respects : ActionsRespect primitives ids)
    {left : Omega Op args outs sigsL} {right : Omega Op args outs sigsR}
    {positions : Fin sigsL.length ≃ Fin sigsR.length} (iso : left.RenumberedBy right positions)
    (schedule : Ordered Op (renameVertex positions) args outs left.toTerm.region right.toTerm.region)
    (identities : ∀ i, ids (unitL, i) (unitR, renameVertex positions i))
    {inputL inputR : Tuple m.Val args} (inputs : TupleRelated m ids inputL inputR) (store : σ) :
    OutcomesRelated m ids σ (renameVertex positions) outs
      (link primitives unitL left inputL store) (link primitives unitR right inputR store) := by
  have boundaries := ((left.renumberedBy_toTerm_iff right positions).mpr iso).exports
  obtain ⟨outcomeL, outcomeR, evaluatedL, evaluatedR, relation⟩ :=
    table_related respects (rename_injective positions) identities schedule boundaries inputs LocalsRelated.empty store
  have actualL : Links primitives unitL left inputL store outcomeL := by
    rw [← left.toGraph_toTerm]
    exact evaluatedL
  have actualR : Links primitives unitR right inputR store outcomeR := by
    rw [← right.toGraph_toTerm]
    exact evaluatedR
  rw [outcome_unique link_spec actualL, outcome_unique link_spec actualR]
  exact relation

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Proofs
