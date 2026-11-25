module

public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Thms

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Partial.Isomorphism.Proofs

universe u v w x
variable {V S : Type u} {Op : Dialect.{u,v} V S}
variable {args outs : Ports (PortType V S)} {past sigs sigs' : List (Ports (PortType V S))}

private noncomputable def option {α : Type*} (p : Part α) : Option α :=
  @Part.toOption α p (Classical.propDecidable _)

private theorem option_bind {α β : Type x} (p : Part α) (f : α → Part β) :
    option (p.bind f) = option p >>= (option ∘ f) := by
  calc
    _ = (option p).elim none (fun a => option (f a)) :=
      @Part.bind_toOption α β f p (Classical.propDecidable _)
        (fun _ => Classical.propDecidable _) (Classical.propDecidable _)
    _ = _ := by cases option p <;> rfl

private theorem option_some {α : Type*} (a : α) : option (Part.some a) = some a :=
  (@Part.toOption_eq_some_iff α (Part.some a) (Classical.propDecidable _) a).mpr
    (Part.mem_some_iff.mpr rfl)

private theorem of_option {α : Type*} (p : Part α) : Part.ofOption (option p) = p :=
  @Part.of_toOption α p (Classical.propDecidable _)

/-- All iteration remains in the Part interpretation of the kind. The
classical conversion represents the result only for the table proof. -/
private noncomputable def evaluate (m : Model.{u,v,w} Op) : KindEvaluator Op m.Val :=
  fun kind children input =>
    option (kind.denoteWith m (fun i x => Part.ofOption (children i x)) input)

private theorem eval_fromTable (m : Model.{u,v,w} Op) (entry : Tuple m.Val args)
    (past sigs : List (Ports (PortType V S))) (locals : Locals m.Val past)
    (nodes : Nodes Op args past sigs) (children : ∀ i, Children (Term Op) (nodes i))
    (results : Wires args (extend past sigs) outs) :
    evalTableWith (evaluate m) entry past sigs locals nodes
        (fun i j x => option ((children i j).denoteOpenWith m x PUnit.unit)) results =
      option ((Term.fromTable past sigs nodes children results).denoteOpenWith m entry locals) := by
  induction sigs generalizing past with
  | nil =>
    simp only [evalTableWith, Term.fromTable, Term.denoteOpenWith]
    exact (option_some _).symm
  | cons head tail ih =>
    simp only [evalTableWith, Term.fromTable, Term.denoteOpenWith, evaluate, of_option]
    rw [show (Bind.bind (m := Part) _ _) = Part.bind _ _ from Part.bind_eq_bind _ _]
    rw [option_bind]
    congr 1
    funext result
    exact ih _ _ _ _ _

private theorem eval_with (m : Model.{u,v,w} Op) (g : Graph Op args past sigs outs)
    (entry : Tuple m.Val args) (locals : Locals m.Val past) :
    g.evalWith (evaluate m) entry locals = option (g.toTerm.denoteOpenWith m entry locals) := by
  induction g with
  | region nodes children results ih =>
    simp only [Graph.evalWith, Graph.toTerm, ← eval_fromTable]
    congr 1
    funext i j input
    exact ih i j input PUnit.unit

theorem observe_eq (m : Model.{u,v,w} Op) {left : Graph Op args [] sigs outs}
    {right : Graph Op args [] sigs' outs} (iso : Graph.Isomorphic Op left right) (input : Tuple m.Val args) :
    observe m left input = observe m right input := by
  have equal := iso.evalWith_eq (evaluate m) input
  have converted := (eval_with m left input PUnit.unit).symm.trans
    (equal.trans (eval_with m right input PUnit.unit))
  exact (of_option _).symm.trans ((congrArg Part.ofOption converted).trans (of_option _))

end Silmaril.SSA.RVSDG.NestedTheta.Partial.Isomorphism.Proofs
