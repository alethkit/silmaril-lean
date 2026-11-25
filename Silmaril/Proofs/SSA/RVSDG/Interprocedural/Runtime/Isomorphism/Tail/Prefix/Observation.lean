module

public import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Table
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Tail.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Prefix.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Thms

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Prefix.Proofs

open Runtime.Isomorphism.Proofs (Rows runRows readRowInput readRowInput_zero readRowInput_succ
  runRows_related readRowInput_related)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {ids : GlobalRel}
variable {args args' outs outs' head : Ports (Ty V S)} {past sigs sigs' : List (Ports (Ty V S))}

private def Primitive (label : NestedTheta.NodeLabel (Instruction Op)) : Prop :=
  match label.kind with
  | .base (.simple (.primitive _)) => True
  | _ => False

private def primitiveOutput (m : Machine.{u, v, w} Op) :
    {ins outs : Ports (Ty V S)} → NestedTheta.Kind (Instruction Op) ins outs →
    Tuple m.Val ins → Option (Tuple m.Val outs)
  | _, _, .base (.simple (.primitive op)), input => some (m.primitive op input)
  | _, _, _, _ => none

private def primitiveRows (nodes : NestedTheta.Nodes (Instruction Op) args past sigs) : Rows m args past sigs :=
  fun i => ⟨(nodes i).ins, (nodes i).inputs, primitiveOutput m (nodes i).kind⟩

private theorem primitiveOutput_related (respects : PrimitivesRespect m ids)
    {left right : NestedTheta.NodeLabel (Instruction Op)} (same : left = right)
    {x : Tuple m.Val left.ins} {y : Tuple m.Val right.ins} (inputs : TupleRelated m ids x y) :
    RunRelated m ids (primitiveOutput m left.kind x) (primitiveOutput m right.kind y) := by
  subst right
  obtain ⟨_, _, kind⟩ := left
  cases kind with
  | theta => exact .none
  | base shape =>
    cases shape with
    | gamma => exact .none
    | simple opcode =>
      cases opcode with
      | primitive op => exact .some (respects op inputs)
      | apply => exact .none

/-- An admitted region either returns after primitives alone, or reaches its
unique nonprimitive vertex. Record the operands before that vertex runs. -/
private inductive LocalObservation (graph : NestedTheta.Graph (Instruction Op) args past sigs outs)
    (entry : Tuple m.Val args) (locals : Locals m.Val past) (outcome : Outcome m outs) : Prop where
  | returned (onlyPrimitives : ∀ i, Primitive (graph.nodes i).label)
      (output : Tuple m.Val outs)
      (computed : runRows entry past sigs locals (primitiveRows graph.nodes) graph.results = some output)
      (observed : outcome = .returned output)
  | terminal (i : Fin sigs.length) (nonPrimitive : ¬ Primitive (graph.nodes i).label)
      (unique : ∀ j, ¬ Primitive (graph.nodes j).label → j = i)
      (values : Tuple m.Val (graph.nodes i).ins)
      (operands : readRowInput entry locals (primitiveRows graph.nodes) i = some values)
      (ports : (graph.nodes i).label.outs = outs)
      (observed : outcome = (ports ▸ exposeKind m (graph.nodes i).kind
        (fun arm input => expose m (graph.children i arm) input) values))

private theorem LocalObservation.prepend
    {graph : NestedTheta.Graph (Instruction Op) args (past ++ [head]) sigs outs}
    {entry : Tuple m.Val args} {locals : Locals m.Val past} {outcome : Outcome m outs}
    {ins : Ports (Ty V S)} (opcode : Op ins head) (wires : Wires args past ins)
    (childSigs : Fin 0 → List (Ports (Ty V S)))
    (children : NestedTheta.Children (NestedTheta.Graph (Instruction Op))
      (⟨ins, .base (.simple (.primitive opcode)), wires, childSigs⟩ :
        NestedTheta.Node (Instruction Op) args past head))
    (h : LocalObservation graph entry (locals.snoc (m.primitive opcode (wires.read entry locals))) outcome) :
    LocalObservation
      (graph.prepend ⟨ins, .base (.simple (.primitive opcode)), wires, childSigs⟩ children)
      entry locals outcome := by
  cases graph with
  | region nodes children' results =>
    cases h with
    | returned onlyPrimitives output computed observed =>
      exact .returned (Fin.cases trivial onlyPrimitives) output computed observed
    | terminal i nonPrimitive unique values operands ports observed =>
      refine .terminal i.succ nonPrimitive
        (Fin.cases (fun h => False.elim (h trivial)) (fun j h => congrArg Fin.succ (unique j h)))
        values ?_ ports observed
      exact (readRowInput_succ entry locals _ _ rfl i).trans operands

private theorem localObservation {term : NestedTheta.Term (Instruction Op) args past sigs outs}
    {entry : Tuple m.Val args} {locals : Locals m.Val past} {outcome : Outcome m outs}
    (safe : outcome ≠ .unsupported) (h : Executes m term entry locals outcome) :
    LocalObservation term.toGraph entry locals outcome := by
  induction h with
  | ret wires entry locals =>
    exact .returned (fun i => i.elim0) _ rfl rfl
  | primitive _ ih =>
    exact LocalObservation.prepend _ _ _ _ (ih safe)
  | @apply args past fn wires _ _ entry locals callee arguments operands =>
    refine .terminal 0 (fun h => h) (fun j _ => Fin.fin_one_eq_zero j) (.cons callee arguments) ?_ rfl ?_
    · exact (readRowInput_zero entry locals _).trans (congrArg some operands)
    · rfl
  | @gamma args inputs outs past arms wires _ children entry locals tag arguments outcome operands selected _ =>
    refine .terminal 0 (fun h => h) (fun j _ => Fin.fin_one_eq_zero j) (.cons tag arguments) ?_ rfl ?_
    · exact (readRowInput_zero entry locals _).trans (congrArg some operands)
    · change outcome = expose m (children tag.selector).toGraph arguments
      rw [expose, NestedTheta.Term.toTerm_toGraph]
      exact ((exposes_iff _ _ _ safe).2 selected).symm

private theorem observe (graph : NestedTheta.Graph (Instruction Op) args [] sigs outs)
    (entry : Tuple m.Val args) (safe : expose m graph entry ≠ .unsupported) :
    LocalObservation graph entry PUnit.unit (expose m graph entry) := by
  have observed := localObservation (term := graph.toTerm) safe
    ((exposes_iff graph.toTerm entry PUnit.unit safe).1 rfl)
  rwa [NestedTheta.Graph.toGraph_toTerm] at observed

private theorem kind_related (respects : PrimitivesRespect m ids)
    {left right : NestedTheta.NodeLabel (Instruction Op)} (same : left = right)
    (runL : Fin left.arity → Tuple m.Val left.kind.entry → Outcome m left.kind.exit)
    (runR : Fin right.arity → Tuple m.Val right.kind.entry → Outcome m right.kind.exit)
    (inputL : Tuple m.Val left.ins) (inputR : Tuple m.Val right.ins)
    (inputs : TupleRelated m ids inputL inputR)
    (arms : ∀ i x y, TupleRelated m ids x y → runL i x ≠ .unsupported →
      runR (Fin.cast (congrArg NestedTheta.NodeLabel.arity same) i) y ≠ .unsupported →
      Outcome.Related m ids (runL i x) (runR (Fin.cast (congrArg NestedTheta.NodeLabel.arity same) i) y))
    (safeL : exposeKind m left.kind runL inputL ≠ .unsupported)
    (safeR : exposeKind m right.kind runR inputR ≠ .unsupported) :
    Outcome.Related m ids (exposeKind m left.kind runL inputL) (exposeKind m right.kind runR inputR) := by
  subst right
  obtain ⟨_, _, kind⟩ := left
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
        | control tag => exact arms tag _ _ args safeL safeR
  | theta => exact False.elim (safeL rfl)

private theorem cast_related {outsL outsR : Ports (Ty V S)} {l : Outcome m outsL} {r : Outcome m outsR}
    (related : Outcome.Related m ids l r) (portsL : outsL = outs) (portsR : outsR = outs') :
    Outcome.Related m ids (portsL ▸ l) (portsR ▸ r) := by
  cases portsL
  cases portsR
  exact related

private theorem safe_of_cast {outsL : Ports (Ty V S)} {outcome : Outcome m outsL}
    (ports : outsL = outs) (safe : (ports ▸ outcome : Outcome m outs) ≠ .unsupported) :
    outcome ≠ .unsupported := by
  cases ports
  exact safe

theorem expose_related (respects : PrimitivesRespect m ids)
    {left : NestedTheta.Graph (Instruction Op) args [] sigs outs}
    {right : NestedTheta.Graph (Instruction Op) args' [] sigs' outs'}
    (iso : NestedTheta.Graph.Isomorphic (Instruction Op) left right)
    (inputL : Tuple m.Val args) (inputR : Tuple m.Val args')
    (inputs : TupleRelated m ids inputL inputR)
    (safeL : expose m left inputL ≠ .unsupported) (safeR : expose m right inputR ≠ .unsupported) :
    Outcome.Related m ids (expose m left inputL) (expose m right inputR) := by
  induction iso with
  | @intro args args' outs outs' sigs sigs' left right _ _ rename labels operands results children ih =>
    let leftRows := primitiveRows (m := m) left.nodes
    let rightRows := primitiveRows (m := m) right.nodes
    have steps i x y (paired : TupleRelated m ids x y) :
        RunRelated m ids ((leftRows i).run x) ((rightRows (rename i)).run y) :=
      primitiveOutput_related respects (labels i) paired
    rcases observe left inputL safeL with ⟨pureL, outputL, runL, observedL⟩ |
      ⟨i, nonPrimitiveL, uniqueL, valuesL, readL, portsL, observedL⟩
    · rcases observe right inputR safeR with ⟨_, outputR, runR, observedR⟩ |
        ⟨j, nonPrimitiveR, _, _, _, _, _⟩
      · have related := runRows_related rename inputL inputR inputs leftRows rightRows
          left.results right.results operands results steps
        rw [runL, runR] at related
        rw [observedL, observedR]
        cases related with | some paired => exact .returned paired
      · exact False.elim (nonPrimitiveR (by
          rw [← rename.apply_symm_apply j, ← labels (rename.symm j)]
          exact pureL (rename.symm j)))
    · rcases observe right inputR safeR with ⟨pureR, _, _, _⟩ |
        ⟨j, _, uniqueR, valuesR, readR, portsR, observedR⟩
      · exact False.elim (nonPrimitiveL (by rw [labels i]; exact pureR (rename i)))
      · have same : rename i = j := uniqueR (rename i) (by rwa [← labels i])
        subst j
        have related := readRowInput_related rename inputL inputR inputs leftRows rightRows operands steps i
        rw [readL, readR] at related
        cases related with
        | some values =>
          have matching := kind_related respects (labels i)
            (fun arm input => expose m (left.children i arm) input)
            (fun arm input => expose m (right.children (rename i) arm) input)
            valuesL valuesR values (ih i)
            (safe_of_cast portsL (observedL ▸ safeL)) (safe_of_cast portsR (observedR ▸ safeR))
          rw [observedL, observedR]
          exact cast_related matching portsL portsR

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Prefix.Proofs
