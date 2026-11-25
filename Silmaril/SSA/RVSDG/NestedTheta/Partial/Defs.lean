module

public import Silmaril.SSA.RVSDG.NestedTheta.Categorical.Defs

/-! # Finite nested execution with partial primitives -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Partial

universe u v w
variable {V S : Type u} {Op : Dialect.{u,v} V S}
variable {args outs carried : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

/-- The assigned primitive action returns a partial result tuple. -/
abbrev Model (Op : Dialect.{u,v} V S) := MonadicModel.{u,v,w} Op Part.{max u w}

def tagged (m : Model.{u,v,w} Op) (again : Bool) (output : Tuple m.Val carried) :
    Tuple m.Val (Theta.BodyResults carried) :=
  .cons ⟨if again then 1 else 0⟩ output

/-- A primitive step has a successful observation. A γ invokes its selected
arm and a θ has a finite sequence of completed body activations. -/
def kindExec (m : Model.{u,v,w} Op) :
    {ins outs : Ports (PortType V S)} → (kind : Kind Op ins outs) →
    (Fin kind.arity → Tuple m.Val kind.entry → Tuple m.Val kind.exit → Prop) →
    Tuple m.Val ins → Tuple m.Val outs → Prop
  | _, _, .base (.simple op), _, input, output => output ∈ m.primitive op input
  | _, _, .base (.gamma _), children, .cons tag payload, output => children tag.down payload output
  | _, _, .theta _, children, input, output =>
    Theta.Iterate (fun x again y => children (0 : Fin 1) x (tagged m again y)) input output

/-- A finite derivation uses the wires of the typed term and resolves each
node before its continuation can read the resulting tuple. -/
def exec (m : Model.{u,v,w} Op) :
    {args outs : Ports (PortType V S)} → {past sigs : List (Ports (PortType V S))} →
    Term Op args past sigs outs → Tuple m.Val args → Locals m.Val past → Tuple m.Val outs → Prop
  | _, _, _, _, .ret wires, input, locals, output => wires.read input locals = output
  | _, _, _, _, .bind node children rest, input, locals, output =>
    ∃ result, kindExec m node.kind (fun j x y => exec m (children j) x PUnit.unit y)
      (node.inputs.read input locals) result ∧ exec m rest input (locals.snoc result) output

def returns (m : Model.{u,v,w} Op) (g : Graph Op args [] sigs outs)
    (input : Tuple m.Val args) (output : Tuple m.Val outs) : Prop :=
  exec m g.toTerm input PUnit.unit output

/-- The Kleisli interpretation of the numbered graph with partial leaves. -/
noncomputable def observe (m : Model.{u,v,w} Op) (g : Graph Op args [] sigs outs)
    (input : Tuple m.Val args) : Part (Tuple m.Val outs) :=
  g.toTerm.denoteOpenWith m input PUnit.unit

end Silmaril.SSA.RVSDG.NestedTheta.Partial
