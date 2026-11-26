module

public import Silmaril.SSA.SeaOfNodes.Loop.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Defs

/-!
# Lower a pure Sea of Nodes loop to one RVSDG θ

The θ carries the original inputs and the current Phi tuple. Its mandatory
first activation tests the source header. The stop tag (0) leaves that
carrier unchanged, so an initially false header completes θ without a
source backedge. The continue tag (1) keeps the original inputs and
installs the whole backedge Phi column.

The preheader and each θ activation emit the source's pure producers in
dependency order. After θ stops, one pure readback vertex evaluates the
return wire in the stopped header environment. This may recompute pure
producers from that final activation. The comparison observes the
returned value and does not count producer firings.
-/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop

open Diamond (Dataflow Model Signature Ty Val ValueSort dataPorts)
open RVSDG (Origin Tuple Wires extend)
open RVSDG.NestedTheta (Term identityPorts)

universe u v w

/-- Split the two typed slices of a carrier. -/
def splitTuple {T : Type u} {F : T → Type w} {right : List T} :
    (left : List T) → Tuple F (left ++ right) → Tuple F left × Tuple F right
  | [], xs => (.nil, xs)
  | _ :: left, .cons x xs =>
    let (front, suffix) := splitTuple left xs
    (.cons x front, suffix)

inductive ThetaOpcode {Data : Type u} (Op : Signature.{u, v} Data) :
    RVSDG.Dialect.{u,max u v} (ValueSort Data) PEmpty.{u+1} where
  | pure {ins : List (ValueSort Data)} {out : ValueSort Data} :
      Op ins out → ThetaOpcode Op (dataPorts ins) [.value out]
  | route (inputs carried : List (ValueSort Data)) :
      ThetaOpcode Op (.value .predicate :: (headerPorts inputs carried ++ dataPorts carried))
        (RVSDG.Theta.BodyResults (headerPorts inputs carried))
  | readExit {args : List (Ty Data)} {sigs : List (List (Ty Data))} {out : ValueSort Data} :
      Dataflow Op args [] sigs → Origin args (extend [] sigs) (.value out) →
        ThetaOpcode Op args [.value out]

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out : ValueSort Data}
variable (g : Loop.Graph Op inputs carried entrySigs headerSigs out) (m : Model.{u, v, w} Op)

abbrev thetaRuntime : RVSDG.Model.{u,max u v,w} (ThetaOpcode Op) where
  value := Diamond.sortValue m.value
  state := fun s => nomatch s
  run
    | .pure op, xs => .cons (m.run op xs) .nil
    | .route inputs carried, .cons predicate xs =>
      let (current, next) := splitTuple (headerPorts inputs carried) xs
      if predicate.down then
        .cons ⟨1⟩ (appendTuple next (splitTuple (dataPorts inputs) current).1)
      else .cons ⟨0⟩ current
    | .readExit header result, xs =>
      .cons (Diamond.read m result xs (header.eval m xs PUnit.unit)) .nil

/-- Compile the ranked pure table before a continuation in the same scope. -/
def lowerFlow {args results : List (Ty Data)} {tail : List (List (Ty Data))} :
    {past sigs : List (List (Ty Data))} → Dataflow Op args past sigs →
    Term (ThetaOpcode Op) args (extend past sigs) tail results →
    Term (ThetaOpcode Op) args past (sigs ++ tail) results
  | _, _, .nil, rest => rest
  | _, _, .cons op inputs more, rest =>
    .bind ⟨_, .base (.simple (.pure op)), inputs, fun j => j.elim0⟩
      (fun j => j.elim0) (lowerFlow more rest)

/-- The argument interface as ordered producer wires. -/
def argWires {T : Type u} (args : List T) (past : List (List T)) : Wires args past args :=
  (identityPorts args).map fun _ => .arg

def allLastWires {args head : List (Ty Data)} (past : List (List (Ty Data))) :
    Wires args (past ++ [head]) head :=
  Diamond.lastWires past (identityPorts head)

abbrev thetaBodySigs (inputs carried : List (ValueSort Data)) (sigs : List (List (Ty Data))) :=
  sigs ++ [RVSDG.Theta.BodyResults (headerPorts inputs carried)]

/-- Run the source header once, then select the RVSDG stop or restart tag.
The backedge wires read the old carrier even when two Phis swap values. -/
def Graph.thetaBody :
    Term (ThetaOpcode Op) (headerPorts inputs carried) []
      (thetaBodySigs inputs carried headerSigs)
      (RVSDG.Theta.BodyResults (headerPorts inputs carried)) :=
  let past := extend [] headerSigs
  let carrier := headerPorts inputs carried
  let payload := appendTuple (g.phiInputs .backedge) (argWires carrier past)
  lowerFlow g.header
    (.bind ⟨_, .base (.simple (.route inputs carried)), .cons g.predicate payload, fun j => j.elim0⟩
      (fun j => j.elim0) (.ret (allLastWires past)))

abbrev thetaSigs (inputs carried : List (ValueSort Data)) (entrySigs : List (List (Ty Data)))
    (out : ValueSort Data) :=
  entrySigs ++ [headerPorts inputs carried, [.value out]]

/-- Wire the initial Phi column into θ and read the result at its stop carrier. -/
def Graph.lowerThetaTerm :
    Term (ThetaOpcode Op) (dataPorts inputs) []
      (thetaSigs inputs carried entrySigs out) [.value out] :=
  let past := extend [] entrySigs
  let carrier := headerPorts inputs carried
  let entry := appendTuple (g.phiInputs .entry) (argWires (dataPorts inputs) past)
  lowerFlow g.preheader
    (.bind ⟨_, .theta carrier, entry, fun _ => thetaBodySigs inputs carried headerSigs⟩
      (fun _ => g.thetaBody)
      (.bind ⟨_, .base (.simple (.readExit g.header g.result)), allLastWires past, fun j => j.elim0⟩
        (fun j => j.elim0) (.ret (allLastWires (past ++ [carrier])))))

/-- The numbered target graph, with one θ and no γ. -/
def Graph.lowerTheta :
    RVSDG.NestedTheta.Graph (ThetaOpcode Op) (dataPorts inputs) [] (thetaSigs inputs carried entrySigs out) [.value out] :=
  g.lowerThetaTerm.toGraph

end Silmaril.SSA.SeaOfNodes.Loop
