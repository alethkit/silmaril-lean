module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Admission.Prefix.Graph.Defs

/-! A structural plan for position-wise aligned δ and φ bindings. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Prefix

universe u v

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {importsL importsR exports : Ports (Ty V S)}
variable {sigsL sigsR : List (Ports (Ty V S))}

/-- Infer binding selections for an aligned pair of term suffixes. -/
def Plan.infer [DecidableEq (Ty V S)] :
    (seeded : Bool) → {pastL sigsL pastR sigsR : List (Ports (Ty V S))} →
    (left : ModuleTerm Op importsL pastL sigsL exports) →
    (right : ModuleTerm Op importsR pastR sigsR exports) →
    Option (Plan Op importsL importsR exports seeded left right)
  | true, _, _, _, _, .ret _, .ret _ => some .done
  | seeded, _, _, _, _, .bind (head := headL) nodeL restL, .bind (head := headR) nodeR restR =>
    match (generalizing := true) headL, nodeL with
    | _, .delta _ =>
      match (generalizing := true) headR, nodeR with
      | _, .delta _ => (Plan.infer seeded restL restR).map fun rest => .skipL (.skipR rest)
      | _, .lambda _ | _, .phi _ => none
    | _, .phi (members := membersL) _ =>
      match (generalizing := true) headR, nodeR with
      | _, .phi (members := membersR) _ =>
        letI : DecidableEq (Function V S) := decideFunction
        if membersL.isEmpty then none
        else if same : membersL = membersR then
          (Plan.infer true restL restR).map fun rest => by
            subst membersR
            cases seeded with
            | false => exact .seed rest
            | true => exact .phi rest
        else none
      | _, .delta _ | _, .lambda _ => none
    | _, .lambda _ => none
  | _, _, _, _, _, _, _ => none
termination_by structural _ _ _ _ _ left _ => left

/-- Align numbered δ and nonempty φ bindings at the same positions. A
pair of δ rows runs through the ordinary linker, the first φ pair seeds
admission, and subsequent φ pairs use fresh-group admission. Each φ pair
must have the same ordered member signatures.

The resulting `GraphPlan` selects only bindings. The admission checker
still checks the actual captures, bodies and dispatch separation. A
missing seed, λ or empty φ row, or unmatched pair rejects this policy. -/
def inferGraphPlan [DecidableEq (Ty V S)] (left : Omega Op importsL exports sigsL)
    (right : Omega Op importsR exports sigsR) : Option (GraphPlan left right) :=
  Plan.infer false left.toTerm.region right.toTerm.region

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Prefix
