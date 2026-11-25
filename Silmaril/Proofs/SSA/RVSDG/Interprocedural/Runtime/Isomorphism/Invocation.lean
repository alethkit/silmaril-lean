module

public import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Table

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Proofs

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {ids : GlobalRel}
variable {args args' outs outs' : Ports (Ty V S)}
variable {past sigs sigs' : List (Ports (Ty V S))}

private abbrev HandlerRespect (m : Machine.{u, v, w} Op) (ids : GlobalRel) (handler : Handler m) :=
  ∀ {ins outs : Ports (Ty V S)} (op : Instruction Op ins outs)
    {x y : Tuple m.Val ins}, TupleRelated m ids x y → RunRelated m ids (handler op x) (handler op y)

private def bodyRows (handler : Handler m) (loops : Nat) (nodes : NestedTheta.Nodes (Instruction Op) args past sigs)
    (children : ∀ i, NestedTheta.Children (NestedTheta.Term (Instruction Op)) (nodes i)) :
    Rows m args past sigs :=
  fun i => ⟨(nodes i).ins, (nodes i).inputs, evalKind m handler loops (nodes i).kind
    (fun j args => evalBody m handler loops (past := []) (children i j) args PUnit.unit)⟩

private theorem body_fromTable (handler : Handler m) (loops : Nat)
    (nodes : NestedTheta.Nodes (Instruction Op) args past sigs)
    (children : ∀ i, NestedTheta.Children (NestedTheta.Term (Instruction Op)) (nodes i))
    (wires : Wires args (extend past sigs) outs) (entry : Tuple m.Val args) (values : Locals m.Val past) :
    evalBody m handler loops (NestedTheta.Term.fromTable past sigs nodes children wires) entry values =
      runRows entry past sigs values (bodyRows handler loops nodes children) wires := by
  induction sigs generalizing past with
  | nil => rfl
  | cons head tail ih =>
    let row : Row m args past head := bodyRows handler loops nodes children 0
    let output := row.run (row.wires.read entry values)
    change output.bind (fun value =>
      evalBody m handler loops (NestedTheta.Term.fromTable (past ++ [head]) tail
        (fun i => nodes i.succ) (fun i => children i.succ) wires) entry (values.snoc value)) =
      output.bind (fun value => runRows entry (past ++ [head]) tail (values.snoc value)
        (bodyRows handler loops (fun i => nodes i.succ) (fun i => children i.succ)) wires)
    exact congrArg (Option.bind output)
      (funext fun output => ih (fun i => nodes i.succ) (fun i => children i.succ) wires (values.snoc output))

private theorem body_graph (handler : Handler m) (loops : Nat)
    (graph : NestedTheta.Graph (Instruction Op) args [] sigs outs) (entry : Tuple m.Val args) :
    evalBody m handler loops (past := []) graph.toTerm entry PUnit.unit =
      runRows entry [] sigs PUnit.unit
        (bodyRows handler loops graph.nodes (fun i arm => (graph.children i arm).toTerm)) graph.results := by
  cases graph with
  | region nodes children wires =>
    exact body_fromTable handler loops nodes (fun i j => (children i j).toTerm) wires entry PUnit.unit

private theorem iterate_related
    (bodyL bodyR : Tuple m.Val args → Option (Tuple m.Val (Theta.BodyResults args)))
    (compatible : ∀ x y, TupleRelated m ids x y → RunRelated m ids (bodyL x) (bodyR y))
    (loops : Nat) (inputL inputR : Tuple m.Val args) (entry : TupleRelated m ids inputL inputR) :
    RunRelated m ids
      (NestedTheta.iterate bodyL (fun tag => tag.selector.val == 1) loops inputL)
      (NestedTheta.iterate bodyR (fun tag => tag.selector.val == 1) loops inputR) := by
  induction loops generalizing inputL inputR with
  | zero => exact .none
  | succ loops ih =>
    have paired := compatible inputL inputR entry
    rw [NestedTheta.iterate, NestedTheta.iterate]
    generalize bodyL inputL = left at paired ⊢
    generalize bodyR inputR = right at paired ⊢
    cases paired with
    | none => exact .none
    | some returns =>
      cases returns with
      | cons control feedback =>
        cases control with
        | control tag =>
          by_cases repeatLoop : (tag.val == 1) = true
          · simp only [Colour.selector, ite_eq_left repeatLoop]
            exact ih _ _ feedback
          · simp only [Colour.selector, ite_eq_right repeatLoop]
            exact .some feedback

private theorem kind_related (handler : Handler m) (steps : HandlerRespect m ids handler)
    (loops : Nat) {left right : NestedTheta.NodeLabel (Instruction Op)}
    (same : left = right)
    (runL : Fin left.arity → Tuple m.Val left.kind.entry → Option (Tuple m.Val left.kind.exit))
    (runR : Fin right.arity → Tuple m.Val right.kind.entry → Option (Tuple m.Val right.kind.exit))
    (inputL : Tuple m.Val left.ins) (inputR : Tuple m.Val right.ins)
    (paired : TupleRelated m ids inputL inputR)
    (subregions : ∀ arm x y, TupleRelated m ids x y →
      RunRelated m ids (runL arm x) (runR (Fin.cast (congrArg NestedTheta.NodeLabel.arity same) arm) y)) :
    RunRelated m ids (evalKind m handler loops left.kind runL inputL)
      (evalKind m handler loops right.kind runR inputR) := by
  subst right
  obtain ⟨ins, outs, kind⟩ := left
  cases kind with
  | base shape =>
    cases shape with
    | simple op => exact steps op paired
    | gamma extra =>
      cases paired with
      | cons tag payload =>
        cases tag with
        | control tag => exact subregions tag _ _ payload
  | theta =>
    let arm : Fin 1 := 0
    exact iterate_related (runL arm) (runR arm) (subregions arm) loops inputL inputR paired

private theorem body_related (handler : Handler m) (steps : HandlerRespect m ids handler) (loops : Nat)
    {left : NestedTheta.Graph (Instruction Op) args [] sigs outs}
    {right : NestedTheta.Graph (Instruction Op) args' [] sigs' outs'}
    (iso : NestedTheta.Graph.Isomorphic (Instruction Op) left right)
    (inputL : Tuple m.Val args) (inputR : Tuple m.Val args') (entry : TupleRelated m ids inputL inputR) :
    RunRelated m ids (evalBody m handler loops (past := []) left.toTerm inputL PUnit.unit)
      (evalBody m handler loops (past := []) right.toTerm inputR PUnit.unit) := by
  induction iso with
  | @intro args args' outs outs' sigs sigs' left right _ _ rename labels operands results _ children =>
    rw [body_graph, body_graph]
    refine runRows_related rename inputL inputR entry _ _ _ _ operands results ?_
    intro i leftInput rightInput related
    exact kind_related handler steps loops (labels i) _ _ leftInput rightInput related (children i)

theorem invoke_related (respects : PrimitivesRespect m ids) (loops calls : Nat) :
    ∀ {params results : Ports (Ty V S)} {calleeL calleeR : m.Val (.value (.function params results))},
      ValueRelated m ids calleeL calleeR → ∀ {argsL argsR : Tuple m.Val params},
      TupleRelated m ids argsL argsR →
      RunRelated m ids (invoke m loops calls calleeL argsL) (invoke m loops calls calleeR argsR) := by
  induction calls with
  | zero => intros; exact .none
  | succ calls ih =>
    intro params results calleeL calleeR related argsL argsR args
    let handler : Handler m := dispatch m (invoke m loops calls)
    have steps : HandlerRespect m ids handler := by
      intro ins outs opcode inputL inputR related
      cases opcode with
      | primitive op => exact .some (respects op related)
      | apply fn =>
        cases related with
        | cons callees arguments => exact ih callees arguments
    cases related with
    | closure captured body =>
      exact body_related handler steps loops body _ _ (prepend_related args captured)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Proofs
