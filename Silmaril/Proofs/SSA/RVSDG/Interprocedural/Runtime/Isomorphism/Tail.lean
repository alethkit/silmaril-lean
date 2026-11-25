module

public import Mathlib.Data.Fintype.Card
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Tail.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Thms
public import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Members

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Proofs

open Recursive.Tail

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {ids : GlobalRel}
variable {args args' outs outs' : Ports (Ty V S)} {sigs sigs' : List (Ports (Ty V S))}

private theorem rename_refl (n : Nat) : renameVertex (Equiv.refl (Fin n)) = id := by
  funext vertex
  unfold renameVertex
  split <;> rfl

private theorem entry_reads {ins ins' : Ports (Ty V S)}
    (wiresL : Wires args [] ins) (wiresR : Wires args [] ins')
    (same : ins = ins') (addresses : wiresL.addresses.map (Address.rename id) = wiresR.addresses)
    {left right : Tuple m.Val args} (inputs : TupleRelated m ids left right) :
    TupleRelated m ids (wiresL.read left PUnit.unit) (wiresR.read right PUnit.unit) := by
  subst ins'
  rw [wires_eq wiresL wiresR addresses]
  exact wireImports_related wiresR inputs

private theorem tailKind_related (respects : PrimitivesRespect m ids)
    {left right : NestedTheta.NodeLabel (Instruction Op)} (same : left = right)
    (runL : Fin left.arity → Tuple m.Val left.kind.entry → Outcome m left.kind.exit)
    (runR : Fin right.arity → Tuple m.Val right.kind.entry → Outcome m right.kind.exit)
    (inputL : Tuple m.Val left.ins) (inputR : Tuple m.Val right.ins)
    (inputs : TupleRelated m ids inputL inputR)
    (arms : ∀ i x y, TupleRelated m ids x y → Outcome.Related m ids (runL i x)
      (runR (Fin.cast (congrArg NestedTheta.NodeLabel.arity same) i) y)) :
    Outcome.Related m ids (exposeKind m left.kind runL inputL) (exposeKind m right.kind runR inputR) := by
  subst right
  obtain ⟨ins, outs, kind⟩ := left
  cases kind with
  | base shape =>
    cases shape with
    | simple instruction =>
      cases instruction with
      | primitive opcode => exact .returned (respects opcode inputs)
      | apply fn =>
        cases inputs with
        | cons callee args => exact .enter (.intro callee args)
    | gamma extra =>
      cases inputs with
      | cons tag args =>
        cases tag with
        | control tag => exact arms tag _ _ args
  | theta => exact .unsupported

theorem expose_related (respects : PrimitivesRespect m ids)
    {left : NestedTheta.Graph (Instruction Op) args [] sigs outs}
    {right : NestedTheta.Graph (Instruction Op) args' [] sigs' outs'}
    (iso : NestedTheta.Graph.Isomorphic (Instruction Op) left right)
    (inputL : Tuple m.Val args) (inputR : Tuple m.Val args')
    (inputs : TupleRelated m ids inputL inputR) :
    Outcome.Related m ids (expose m left inputL) (expose m right inputR) := by
  induction iso with
  | @intro args args' outs outs' sigs sigs' left right entry exit rename labels operands results children ih =>
    subst args' outs'
    have length : sigs.length = sigs'.length := by
      simpa only [Fintype.card_fin] using Fintype.card_congr rename
    cases sigs with
    | nil =>
      have empty : sigs' = [] := List.length_eq_zero_iff.mp length.symm
      subst sigs'
      have fixed : rename = Equiv.refl (Fin 0) := Equiv.ext (fun i => i.elim0)
      subst rename
      cases left with
      | region nodesL armsL wiresL =>
        cases right with
        | region nodesR armsR wiresR =>
          change wiresL.addresses.map (Address.rename (renameVertex (Equiv.refl (Fin 0)))) =
            wiresR.addresses at results
          rw [rename_refl] at results
          exact .returned (entry_reads wiresL wiresR rfl results inputs)
    | cons head tail =>
      cases sigs' with
      | nil => cases length
      | cons head' tail' =>
        have tails : tail.length = tail'.length := Nat.succ.inj length
        cases tail with
        | cons second rest =>
          cases tail' with
          | nil => cases tails
          | cons second' rest' =>
            cases left
            cases right
            exact .unsupported
        | nil =>
          have empty : tail' = [] := List.length_eq_zero_iff.mp tails.symm
          subst tail'
          have fixed : rename = Equiv.refl (Fin 1) := Equiv.ext fun i =>
            (Fin.fin_one_eq_zero (rename i)).trans (Fin.fin_one_eq_zero i).symm
          subst rename
          have headEq : head = head' := congrArg NestedTheta.NodeLabel.outs (labels 0)
          subst head'
          cases left with
          | region nodesL armsL wiresL =>
            cases right with
            | region nodesR armsR wiresR =>
              change wiresL.addresses.map (Address.rename (renameVertex (Equiv.refl (Fin 1)))) =
                wiresR.addresses at results
              rw [rename_refl] at results
              have wiresEq : wiresL = wiresR := wires_eq wiresL wiresR results
              subst wiresR
              erw [expose_singleton m nodesL armsL wiresL inputL,
                expose_singleton m nodesR armsR wiresL inputR, exposeSingleton, exposeSingleton]
              classical
              by_cases same : head = outs
              · subst outs
                erw [dite_eq_left (show head = head by rfl), dite_eq_left (show head = head by rfl)]
                by_cases forwarded : wiresL = forwarding args head
                · erw [ite_eq_left forwarded, ite_eq_left forwarded]
                  have label : (nodesL 0).label = (nodesR 0).label := labels 0
                  have addresses := operands 0
                  change (nodesL 0).inputs.addresses.map (Address.rename (renameVertex (Equiv.refl (Fin 1)))) =
                    (nodesR 0).inputs.addresses at addresses
                  rw [rename_refl] at addresses
                  have operandsRelated := entry_reads (nodesL 0).inputs (nodesR 0).inputs
                    (congrArg NestedTheta.NodeLabel.ins label) addresses inputs
                  exact tailKind_related respects label _ _ _ _ operandsRelated (ih 0)
                · erw [ite_eq_right forwarded, ite_eq_right forwarded]
                  exact .unsupported
              · erw [dite_eq_right same, dite_eq_right same]
                exact .unsupported

theorem inspect_related (respects : PrimitivesRespect m ids) {a b : Activation m outs}
    (paired : Activation.Related m ids a b) : Outcome.Related m ids (inspect m a) (inspect m b) := by
  cases paired with
  | intro callee inputs =>
    obtain ⟨values, body⟩ := Recursive.resolve_related callee
    exact expose_related respects body _ _ (prepend_related inputs values)

theorem diverges_iff (respects : PrimitivesRespect m ids) {a b : Activation m outs}
    (paired : Activation.Related m ids a b) : Diverges m a ↔ Diverges m b := by
  constructor
  · intro infinite
    apply InfiniteTrace.coinduct (fun b => ∃ a, Activation.Related m ids a b ∧ Diverges m a)
    · rintro b ⟨a, related, infinite⟩
      obtain ⟨a', edge, tail⟩ := InfiniteTrace.unfold infinite
      have matched := inspect_related respects related
      rw [show inspect m a = .enter a' from edge] at matched
      generalize step : inspect m b = outcome at matched
      cases matched with
      | enter next => exact ⟨_, step, a', next, tail⟩
    · exact ⟨a, paired, infinite⟩
  · intro infinite
    apply InfiniteTrace.coinduct (fun a => ∃ b, Activation.Related m ids a b ∧ Diverges m b)
    · rintro a ⟨b, related, infinite⟩
      obtain ⟨b', edge, tail⟩ := InfiniteTrace.unfold infinite
      have matched := inspect_related respects related
      rw [show inspect m b = .enter b' from edge] at matched
      generalize step : inspect m a = outcome at matched
      cases matched with
      | enter next => exact ⟨_, step, b', next, tail⟩
    · exact ⟨b, paired, infinite⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Proofs
