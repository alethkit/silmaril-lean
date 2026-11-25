module

public import Silmaril.SSA.RVSDG.NestedTheta.Equality.Thms

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Equality

universe u v
variable {V S : Type u} {Op : Dialect.{u,v} V S}
variable {args ins outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}
variable [DecidableEq (PortType V S)]
variable (code : OpcodeCode Op) [DecidableEq code.Key]

private def decideWires (x y : Wires args past ins) : Decidable (x = y) :=
  decidable_of_iff (x.addresses = y.addresses)
    ⟨addresses_injective x y, congrArg Wires.addresses⟩

private def decideKind (x y : Kind Op ins outs) : Decidable (x = y) :=
  decidable_of_iff (kindCode code x = kindCode code y)
    ⟨kind_injective code x y, congrArg (kindCode code)⟩

private def decideNode (x y : Node Op args past outs) : Decidable (x = y) := by
  obtain ⟨i, k, wires, children⟩ := x
  obtain ⟨i', k', wires', children'⟩ := y
  refine if same : i = i' then ?_ else .isFalse (fun equal => same (congrArg Node.ins equal))
  subst i'
  letI := decideKind code k k'
  refine if same : k = k' then ?_ else .isFalse (fun equal => same ?_)
  · subst k'
    letI := decideWires wires wires'
    refine if same : wires = wires' then ?_ else .isFalse (fun equal => same ?_)
    · subst wires'
      refine if same : ∀ j, children j = children' j then ?_ else .isFalse (fun equal => same ?_)
      · exact .isTrue (by rw [funext same])
      · cases equal
        exact fun _ => rfl
    · cases equal
      rfl
  · cases equal
    rfl

private def decideTerm :
    {args outs : Ports (PortType V S)} → {past sigs : List (Ports (PortType V S))} →
    (x y : Term Op args past sigs outs) → Decidable (x = y)
  | _, _, _, _, .ret ws, .ret vs =>
    letI := decideWires ws vs
    decidable_of_iff (ws = vs) ⟨congrArg Term.ret, fun h => Term.ret.inj h⟩
  | _, _, _, _, .bind node children rest, .bind node' children' rest' => by
    letI := decideNode code node node'
    refine if same : node = node' then ?_ else .isFalse (fun h => same ?_)
    · subst node'
      letI (j : Fin node.kind.arity) : Decidable (children j = children' j) :=
        decideTerm (children j) (children' j)
      refine if same : ∀ j, children j = children' j then ?_ else .isFalse (fun h => same ?_)
      · have heq := funext same
        subst children'
        letI := decideTerm rest rest'
        refine if same : rest = rest' then .isTrue (congrArg (Term.bind node children) same) else
          .isFalse (fun h => same ?_)
        cases h
        rfl
      · cases h
        exact fun _ => rfl
    · cases h
      rfl
termination_by structural _ _ _ _ x _ => x

/-- Compare every nested region and every input and result address. -/
def decideGraph (x y : Graph Op args past sigs outs) : Decidable (x = y) :=
  letI := decideTerm code x.toTerm y.toTerm
  decidable_of_iff (x.toTerm = y.toTerm)
    ⟨fun h => by simpa only [Graph.toGraph_toTerm] using congrArg Term.toGraph h, congrArg Graph.toTerm⟩

end Silmaril.SSA.RVSDG.NestedTheta.Equality
