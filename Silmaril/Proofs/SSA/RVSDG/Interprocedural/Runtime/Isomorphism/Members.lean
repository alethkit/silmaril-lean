module

public import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Values

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Proofs

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {ids : GlobalRel}
variable {args ins : Ports (Ty V S)} {past : List (Ports (Ty V S))}

theorem memberValues_related (members : List (Function V S))
    (left right : (i : Fin members.length) → m.Val members[i].port)
    (related : ∀ i, ValueRelated m ids (left i) (right i)) :
    TupleRelated m ids (memberValues members left) (memberValues members right) := by
  induction members with
  | nil => exact .nil
  | cons first rest ih => exact .cons (related 0) (ih _ _ fun i => related i.succ)

private theorem memberPrefix_related (members : List (Function V S)) (count : Nat)
    (left right : (i : Fin members.length) → m.Val members[i].port)
    (related : ∀ i, ValueRelated m ids (left i) (right i)) :
    ∀ i, TupleRelated m ids ((memberPrefix members count left).get i)
      ((memberPrefix members count right).get i) := by
  induction members generalizing count with
  | nil =>
    cases count <;> exact fun i => i.elim0
  | cons first rest ih =>
    cases count with
    | zero => exact fun i => i.elim0
    | succ count =>
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact .cons (related 0) .nil
      · exact ih count _ _ (fun k => related k.succ) j

private theorem port_eq {ports : Ports (Ty V S)} {t : Ty V S} (left right : Port ports t)
    (same : left.index = right.index) : left = right := by
  induction left with
  | head =>
    cases right with
    | head => rfl
    | tail port => cases same
  | tail port ih =>
    cases right with
    | head => cases same
    | tail other => exact congrArg Port.tail (ih other (Nat.succ.inj same))

private theorem origin_eq {t : Ty V S} (left right : Origin args past t)
    (same : Address.rename id left.address = right.address) : left = right := by
  cases left with
  | arg p =>
    cases right with
    | arg q => exact congrArg Origin.arg (port_eq p q (Address.arg.inj same))
    | output j q => cases same
  | output i p =>
    cases right with
    | arg q => cases same
    | output j q =>
      have equal : i = j := Fin.ext (Address.output.inj same).1
      subst j
      exact congrArg (Origin.output i) (port_eq p q (Address.output.inj same).2)

theorem wires_eq (left right : Wires args past ins)
    (same : left.addresses.map (Address.rename id) = right.addresses) : left = right := by
  induction left with
  | nil => cases right; rfl
  | cons source rest ih =>
    cases right with
    | cons target tail =>
      have ⟨first, more⟩ := List.cons.inj same
      rw [origin_eq source target first, ih tail more]

private theorem read_same_related (wires : Wires args past ins) {left right : Tuple m.Val args}
    (inputs : TupleRelated m ids left right) {pastL pastR : Locals m.Val past}
    (locals : ∀ i, TupleRelated m ids (pastL.get i) (pastR.get i)) :
    TupleRelated m ids (wires.read left pastL) (wires.read right pastR) := by
  induction wires with
  | nil => exact .nil
  | cons source rest ih =>
    cases source with
    | arg p => exact .cons (get_related inputs p) ih
    | output i p => exact .cons (get_related (locals i) p) ih

private theorem close_related {fn : Function V S} (left right : Lambda Op args past fn)
    (iso : left.Renumbered id right) {inputL inputR : Tuple m.Val args}
    (inputs : TupleRelated m ids inputL inputR) {pastL pastR : Locals m.Val past}
    (locals : ∀ i, TupleRelated m ids (pastL.get i) (pastR.get i)) :
    TupleRelated m ids (Lambda.close Op left inputL pastL).values
      (Lambda.close Op right inputR pastR).values := by
  obtain ⟨contextL, wiresL, sigsL, bodyL⟩ := left
  obtain ⟨contextR, wiresR, sigsR, bodyR⟩ := right
  obtain ⟨⟨same, wires⟩, _⟩ := iso
  change contextL = contextR at same
  subst contextR
  change TupleRelated m ids (wiresL.read inputL pastL) (wiresR.read inputR pastR)
  rw [wires_eq wiresL wiresR wires]
  exact read_same_related wiresR inputs locals

theorem resolve_related {params results : Ports (Ty V S)}
    {left right : m.Val (.value (.function params results))}
    (related : ValueRelated m ids left right) :
    TupleRelated m ids (resolve m left).values (resolve m right).values ∧
      NestedTheta.Graph.Isomorphic (Instruction Op) (resolve m left).body (resolve m right).body := by
  cases related with
  | closure captured body => exact ⟨captured, body⟩
  | @member context members left right tableL tableR captured definitions slot =>
    let refL (i : Fin members.length) := Colour.member left tableL i
    let refR (i : Fin members.length) := Colour.member right tableR i
    have refs (i : Fin members.length) : ValueRelated m ids (refL i) (refR i) :=
      .member captured definitions i
    have entry := prepend_related (memberValues_related members refL refR refs) captured
    have earlierMembers := memberPrefix_related members slot.val refL refR refs
    have selected := definitions slot
    exact ⟨close_related (tableL slot) (tableR slot) selected entry earlierMembers, selected.2⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Proofs
