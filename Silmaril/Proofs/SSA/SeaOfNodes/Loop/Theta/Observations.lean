module

public import Silmaril.Proofs.SSA.SeaOfNodes.Loop.Theta.Correctness
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Defs
import Silmaril.SSA.RVSDG.NestedTheta.Partial.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.ThetaProofs

open RVSDG (Dialect Locals PortType Ports Tuple)
open RVSDG.NestedTheta (Kind MonadicModel Term)

universe u v w

section TotalPrimitives

variable {V S : Type u} {Op : Dialect.{u,v} V S}
variable {ins outs args : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

/-- Embedding a total primitive interpretation into Part preserves the
finite relation. This only uses successful observations of primitives. -/
private theorem kind_partial_iff (m : RVSDG.Model.{u,v,w} Op) (kind : Kind Op ins outs)
    (total kleisli : Fin kind.arity → Tuple m.Val kind.entry → Tuple m.Val kind.exit → Prop)
    (child : ∀ i x y, total i x y ↔ kleisli i x y)
    (input : Tuple m.Val ins) (output : Tuple m.Val outs) :
    kind.Exec m total input output ↔
      RVSDG.NestedTheta.Partial.kindExec (MonadicModel.ofRuntime m) kind kleisli input output := by
  cases kind with
  | base shape =>
    cases shape with
    | simple op => exact eq_comm.trans Part.mem_some_iff.symm
    | gamma =>
      cases input with
      | cons tag payload => exact child tag.down payload output
  | theta =>
    have body (x y : Tuple m.Val ins) (again : Bool) :=
      child (0 : Fin 1) x (RVSDG.Theta.bodyResult m again y)
    constructor
    · intro run
      induction run with
      | stop last => exact .stop ((body _ _ false).mp last)
      | again next _ ih => exact .again ((body _ _ true).mp next) ih
    · intro run
      induction run with
      | stop last => exact .stop ((body _ _ false).mpr last)
      | again next _ ih => exact .again ((body _ _ true).mpr next) ih

private theorem exec_partial_iff (m : RVSDG.Model.{u,v,w} Op) (t : Term Op args past sigs outs)
    (input : Tuple m.Val args) (locals : Locals m.Val past) (output : Tuple m.Val outs) :
    t.Exec m input locals output ↔ RVSDG.NestedTheta.Partial.exec (MonadicModel.ofRuntime m) t input locals output := by
  induction t with
  | ret => rfl
  | bind node children rest child_iff rest_iff =>
    refine exists_congr fun values => ?_
    exact (kind_partial_iff m node.kind _ _ (fun i x y => child_iff i x PUnit.unit y) _ _).and
      (rest_iff input (locals.snoc values) output)

end TotalPrimitives

open Diamond (Model Signature Ty Val ValueSort dataPorts sortValue)

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out : ValueSort Data}
variable (g : Graph Op inputs carried entrySigs headerSigs out) (m : Model.{u,v,w} Op)
variable (input : Tuple (Val m.value) (dataPorts inputs)) (result : sortValue m.value out)

theorem lower_observe :
    g.Returns m input result ↔
      RVSDG.NestedTheta.Partial.observe (MonadicModel.ofRuntime (thetaRuntime m)) g.lowerTheta input =
        Part.some (.cons result .nil) :=
  (lower_returns g m input result).trans
    ((g.lowerTheta.returns_iff (thetaRuntime m) input _).trans
      ((exec_partial_iff (thetaRuntime m) g.lowerTheta.toTerm input PUnit.unit _).trans
        (RVSDG.NestedTheta.Partial.observe_eq_some _ _ _ _).symm))

theorem lower_finishes :
    g.Returns m input result ↔
      RVSDG.NestedTheta.Petri.Finishes (thetaRuntime m) g.lowerTheta input (.cons result .nil) :=
  (lower_returns g m input result).trans (RVSDG.NestedTheta.Petri.finishes_iff _ _ _ _).symm

end Silmaril.SSA.SeaOfNodes.Loop.ThetaProofs
