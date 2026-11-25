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

private theorem step_right (respects : PrimitivesRespect m ids) {a b a' : Activation m outs}
    (paired : Activation.Related m ids a b) (edge : Step m a a') :
    ∃ b', Step m b b' ∧ Activation.Related m ids a' b' := by
  have matched := inspect_related respects paired
  rw [show inspect m a = .enter a' from edge] at matched
  generalize step : inspect m b = outcome at matched
  cases matched with
  | enter next => exact ⟨_, step, next⟩

private theorem step_left (respects : PrimitivesRespect m ids) {a b b' : Activation m outs}
    (paired : Activation.Related m ids a b) (edge : Step m b b') :
    ∃ a', Step m a a' ∧ Activation.Related m ids a' b' := by
  have matched := inspect_related respects paired
  rw [show inspect m b = .enter b' from edge] at matched
  generalize step : inspect m a = outcome at matched
  cases matched with
  | enter next => exact ⟨_, step, next⟩

private theorem match_stream (P : Activation m outs → Activation m outs → Prop)
    (matchesStep : ∀ {a b a'}, P a b → Step m a a' → ∃ b', Step m b b' ∧ P a' b')
    (source : Nat → Activation m outs) (steps : ∀ n, Step m (source n) (source (n + 1)))
    (target : Activation m outs) (initial : P (source 0) target) :
    ∃ run : Nat → Activation m outs, run 0 = target ∧
      (∀ n, Step m (run n) (run (n + 1))) ∧ ∀ n, P (source n) (run n) := by
  classical
  let next (n : Nat) (current : {state // P (source n) state}) :
      {state // Step m current.val state ∧ P (source (n + 1)) state} :=
    Classical.indefiniteDescription _ (matchesStep current.property (steps n))
  let run : (n : Nat) → {state // P (source n) state} :=
    Nat.rec ⟨target, initial⟩ (fun n current => ⟨(next n current).val, (next n current).property.2⟩)
  exact ⟨fun n => (run n).val, rfl, fun n => (next n (run n)).property.1, fun n => (run n).property⟩

theorem stream_right (respects : PrimitivesRespect m ids) {a b : Activation m outs}
    (paired : Activation.Related m ids a b) (left : Nat → Activation m outs) (initial : left 0 = a)
    (steps : ∀ n, Step m (left n) (left (n + 1))) :
    ∃ right : Nat → Activation m outs, right 0 = b ∧
      (∀ n, Step m (right n) (right (n + 1))) ∧ ∀ n, Activation.Related m ids (left n) (right n) :=
  match_stream (Activation.Related m ids) (step_right respects) left steps b (initial.symm ▸ paired)

theorem stream_left (respects : PrimitivesRespect m ids) {a b : Activation m outs}
    (paired : Activation.Related m ids a b) (right : Nat → Activation m outs) (initial : right 0 = b)
    (steps : ∀ n, Step m (right n) (right (n + 1))) :
    ∃ left : Nat → Activation m outs, left 0 = a ∧
      (∀ n, Step m (left n) (left (n + 1))) ∧ ∀ n, Activation.Related m ids (left n) (right n) :=
  match_stream (fun b a => Activation.Related m ids a b) (step_left respects) right steps a (initial.symm ▸ paired)

theorem diverges_iff (respects : PrimitivesRespect m ids) {a b : Activation m outs}
    (paired : Activation.Related m ids a b) : Diverges m a ↔ Diverges m b := by
  constructor
  · rintro ⟨left, initial, steps⟩
    obtain ⟨right, initial, steps, _⟩ := stream_right respects paired left initial steps
    exact ⟨right, initial, steps⟩
  · rintro ⟨right, initial, steps⟩
    obtain ⟨left, initial, steps, _⟩ := stream_left respects paired right initial steps
    exact ⟨left, initial, steps⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Proofs
