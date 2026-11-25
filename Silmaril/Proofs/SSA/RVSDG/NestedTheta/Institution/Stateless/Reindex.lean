module

public import Silmaril.SSA.RVSDG.NestedTheta.Institution.Stateless.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Institution.Thms

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Institution.Stateless.Proofs

open CategoryTheory
open OrderedRuntime.Structured (Values Ty)
open RVSDG.Institution (OpcodeMap)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
variable {V : Type u} {P Q : Dialect.{u,v} V PUnit.{u+1}}
variable {args outs : Ports (Ty V)} {past sigs : List (Ports (Ty V))}

theorem noState_map (f : OpcodeMap P Q) (t : Term P args past sigs outs) :
    NoState (Institution.mapTerm f t) ↔ NoState t := by
  induction t with
  | ret => rfl
  | bind node children rest ihChildren ihRest =>
    obtain ⟨ins, kind, inputs, childrenSig⟩ := node
    cases kind
    case' base shape => cases shape
    all_goals
      simp only [Institution.mapTerm, NoState, ihRest]
      exact and_congr Iff.rfl (and_congr Iff.rfl (and_congr (forall_congr' ihChildren) Iff.rfl))

variable {A B : Signature.{u,v} V}

theorem observe_map (f : A ⟶ B) (m : Model.{u,v,w} B) (g : Graph A.op args [] sigs outs)
    (input : Tuple (Values m.value) args) :
    observe m (Institution.mapGraph (Institution.Partial.Signature.Hom.opcodeMap f) g) input =
      observe (reduct f m) g input := by
  unfold observe NestedTheta.Partial.observe Institution.mapGraph
  rw [Term.toTerm_toGraph]
  rw [Institution.denoteOpen_map (Institution.Partial.Signature.Hom.opcodeMap f) m.partial g.toTerm input PUnit.unit]
  refine congrArg (fun
      (primitive : ∀ {ins outs : Ports (Ty V)}, A.op ins outs → Tuple (Values m.value) ins →
        Part (Tuple (Values m.value) outs)) =>
    show Part (Tuple (Values m.value) outs) from
      g.toTerm.denoteOpenWith
        (⟨m.value, fun _ => PUnit, primitive⟩ : MonadicModel.{u,v,max u w} A.op Part) input PUnit.unit) ?_
  funext ins outs op values
  cases op with
  | pure _ => rfl
  | effect op => exact PEmpty.elim op

end Silmaril.SSA.RVSDG.NestedTheta.Institution.Stateless.Proofs
