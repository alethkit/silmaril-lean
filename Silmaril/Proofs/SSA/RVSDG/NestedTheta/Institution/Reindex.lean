module

public import Silmaril.SSA.RVSDG.NestedTheta.Institution.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Thms

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Institution.Proofs

open CategoryTheory
open RVSDG.Institution (OpcodeMap)
open OrderedRuntime.Structured (Instruction Values Ty)
open Silmaril.Elgot (Iterate)

universe u v w
variable {V S : Type u} {P Q R : Dialect.{u,v} V S}
variable {args outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem mapTerm_id (t : Term P args past sigs outs) : mapTerm (fun op => op) t = t := by
  induction t with
  | ret => rfl
  | bind node children rest ihChildren ihRest =>
    obtain ⟨ins, kind, inputs, childSigs⟩ := node
    cases kind with
    | base shape =>
      cases shape <;> simp only [mapTerm, ihChildren, ihRest]
    | theta => simp only [mapTerm, ihChildren, ihRest]

private theorem mapTerm_comp (f : OpcodeMap P Q) (g : OpcodeMap Q R) (t : Term P args past sigs outs) :
    mapTerm (fun op => g (f op)) t = mapTerm g (mapTerm f t) := by
  induction t with
  | ret => rfl
  | bind node children rest ihChildren ihRest =>
    obtain ⟨ins, kind, inputs, childSigs⟩ := node
    cases kind with
    | base shape =>
      cases shape <;> simp only [mapTerm, ← ihChildren, ← ihRest]
    | theta => simp only [mapTerm, ← ihChildren, ← ihRest]

theorem mapGraph_id (g : Graph P args past sigs outs) : mapGraph (fun op => op) g = g := by
  rw [mapGraph, mapTerm_id, Graph.toGraph_toTerm]

theorem mapGraph_comp (f : OpcodeMap P Q) (g : OpcodeMap Q R) (t : Graph P args past sigs outs) :
    mapGraph (fun op => g (f op)) t = mapGraph g (mapGraph f t) := by
  simp only [mapGraph, Term.toTerm_toGraph, mapTerm_comp]

/-- The syntactic map commutes with arbitrary shared Kleisli interpretation,
including the θ branch and calls in nested arms. -/
theorem denoteOpen_map {m : Type (max u w) → Type (max u w)} [Monad m] [Iterate m]
    (f : OpcodeMap P Q) (model : MonadicModel.{u,v,w} Q m) (t : Term P args past sigs outs)
    (input : Tuple model.Val args) (locals : Locals model.Val past) :
    (mapTerm f t).denoteOpenWith model input locals = t.denoteOpenWith (monadicReduct f model) input locals := by
  induction t with
  | ret => rfl
  | bind node children rest ihChildren ihRest =>
    obtain ⟨ins, kind, inputs, childSigs⟩ := node
    cases kind with
    | base shape =>
      cases shape with
      | simple => simp only [mapTerm, Term.denoteOpenWith, Kind.denoteWith, monadicReduct, ihRest]
      | gamma =>
        simp only [mapTerm, Term.denoteOpenWith, Kind.denoteWith, ihChildren, ihRest]
        generalize inputs.read input locals = selector
        cases selector
        rfl
    | theta =>
      simp only [mapTerm, Term.denoteOpenWith, Kind.denoteWith, ihChildren, ihRest]
      rfl

variable {A B C : Signature.{u,v} V} {σ : Type (max u w)}

theorem observe_map {args outs : Ports (Ty V)} {sigs : List (Ports (Ty V))}
    (f : A ⟶ B) (model : Model.{u,v,w} B σ) (g : Graph A.op args [] sigs outs)
    (input : Tuple (Values model.value) args) (store : σ) :
    OrderedState.observe model (mapGraph (Signature.opcodeMap f) g) input store =
      OrderedState.observe (reduct f model) g input store := by
  unfold OrderedState.observe mapGraph
  rw [Term.toTerm_toGraph]
  change ((mapTerm (Signature.opcodeMap f) g.toTerm).denoteOpenWith
    (OrderedState.interpretation model) input PUnit.unit).run store =
    (g.toTerm.denoteOpenWith (OrderedState.interpretation (reduct f model)) input PUnit.unit).run store
  rw [denoteOpen_map]
  unfold OrderedState.interpretation monadicReduct
  refine congrArg (fun
      (primitive : ∀ {ins outs : Ports (Ty V)}, A.op ins outs → Tuple (Values model.value) ins →
        StateT σ _root_.Part (Tuple (Values model.value) outs)) =>
    show _root_.Part (OrderedState.Configuration model.value σ outs) from
      (g.toTerm.denoteOpenWith (⟨model.value, fun _ => PUnit, primitive⟩ :
        MonadicModel.{u,v,max u w} A.op (StateT σ _root_.Part)) input PUnit.unit).run store) ?_
  funext ins outs op values
  cases op <;> rfl

private theorem opcode_id {ins out : Ports (Ty V)} (op : A.op ins out) : Signature.opcodeMap (𝟙 A) op = op := by
  cases op <;> rfl

private theorem opcode_comp {ins out : Ports (Ty V)} (f : A ⟶ B) (g : B ⟶ C) (op : A.op ins out) :
    Signature.opcodeMap (f ≫ g) op = Signature.opcodeMap g (Signature.opcodeMap f op) := by
  cases op <;> rfl

theorem equation_map_id (e : Equation A) : e.map (𝟙 A) = e := by
  have ops : @Signature.opcodeMap _ _ _ (𝟙 A) = (fun _ _ op => op) :=
    funext fun _ => funext fun _ => funext (opcode_id (A := A))
  cases e
  simp only [Equation.map, ops, mapGraph_id]

theorem equation_map_comp (f : A ⟶ B) (g : B ⟶ C) (e : Equation A) :
    e.map (f ≫ g) = (e.map f).map g := by
  have ops : @Signature.opcodeMap _ _ _ (f ≫ g) =
      (fun _ _ op => Signature.opcodeMap g (Signature.opcodeMap f op)) :=
    funext fun _ => funext fun _ => funext (opcode_comp f g)
  cases e
  simp only [Equation.map, ops, mapGraph_comp]

theorem reductFunctor_id (A : Signature.{u,v} V) :
    reductFunctor (σ := σ) (𝟙 A) = 𝟭 (Discrete (Model A σ)) :=
  CategoryTheory.Functor.ext (fun m => by cases m; rfl)

theorem reductFunctor_comp (f : A ⟶ B) (g : B ⟶ C) :
    reductFunctor (σ := σ) (f ≫ g) = reductFunctor g ⋙ reductFunctor f := by
  apply Discrete.functor_ext
  intro model
  rfl

theorem holds_iff_finite (e : Equation A) (model : Model.{u,v,w} A σ) :
    e.Holds model ↔ ∀ (input : Tuple (Values model.value) e.args) (initial : σ)
      (output : OrderedState.Configuration model.value σ e.outs),
      OrderedState.exec model e.lhs.toTerm input PUnit.unit initial output ↔
        OrderedState.exec model e.rhs.toTerm input PUnit.unit initial output := by
  constructor
  · intro h input initial output
    rw [← OrderedState.mem_observe, ← OrderedState.mem_observe, h input initial]
  · intro h input initial
    apply Part.ext
    intro output
    rw [OrderedState.mem_observe, OrderedState.mem_observe]
    exact h input initial output

end Silmaril.SSA.RVSDG.NestedTheta.Institution.Proofs
