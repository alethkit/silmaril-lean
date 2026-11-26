module

public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Fuel.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Fuel.Correctness

/-! # The CFG runner charges exactly one visit beyond the backedges taken -/

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Fuel

open Diamond (Model Val ValueSort dataPorts)
open Diamond.LambdaSSA (inputEnv)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Diamond.Signature.{u, v} Data} [DecidableEq Data]
variable {inputs carried : List (ValueSort Data)}
variable {entrySigs headerSigs : List (List (Diamond.Ty Data))} {out : ValueSort Data}
variable (g : Graph Op inputs carried entrySigs headerSigs out)
variable (m : Model.{u, v, w} Op) (input : Tuple (Val m.value) (dataPorts inputs))

/-- With fuel for the terminating visit as well as the backedges, running the
generated syntax has exactly the graph's bounded observation. -/
theorem run_succ (budget : Nat) :
    run m (inputEnv m input) (budget + 1) (lower g) =
      (g.evalBackedges m budget input).map (fun result => (0, packResult m result)) :=
  Proofs.run_succ m g input budget

theorem run_zero : run m (inputEnv m input) 0 (lower g) = none :=
  Proofs.run_zero m g input

end Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Fuel
