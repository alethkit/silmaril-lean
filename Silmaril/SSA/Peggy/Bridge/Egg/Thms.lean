module

public import Silmaril.SSA.Peggy.Bridge.Egg.Defs
import Silmaril.Proofs.SSA.Peggy.Bridge.Egg.Sound

@[expose] public section

namespace Silmaril.SSA.Peggy.Bridge.Egg

open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Egg
open Acyclic (Interpretation Ranked)

variable {Data : Type} {P : PEG.InstructionSet Data}
variable {params results : List (PEG.Ty Data)} {n n' : Nat}
variable {g : PEG.Graph P params results n 0} {g' : PEG.Graph P params results n' 0}

/-- Unfolding a typed vertex preserves its partial value. -/
theorem encode_eval (r : Ranked g) (M : Interpretation P) (ρ : M.Inputs params) (i : Fin n) :
    (encode r i).eval (model M) ρ = r.eval M ρ i :=
  Silmaril.Proofs.SSA.Peggy.Bridge.Egg.encode_eval r M ρ i

theorem encodeOutputs_eval (r : Ranked g) (M : Interpretation P) (ρ : M.Inputs params)
    (i : Fin results.length) :
    (encodeOutputs r i).eval (model M) ρ = r.evalOutputs M ρ i :=
  Silmaril.Proofs.SSA.Peggy.Bridge.Egg.encodeOutputs_eval r M ρ i

/-- Every accepted certificate preserves the entire ordered output vector at
the same inputs, for every interpretation satisfying the declared rules. -/
theorem outputs_sound {rs : List (Core.Rule (signature P))} {r : Ranked g} {r' : Ranked g'}
    (cert : OutputsExplained rs r r') (M : Interpretation P)
    (hrules : ∀ rule ∈ rs, rule.Holds (model M)) (ρ : M.Inputs params) :
    r.evalOutputs M ρ = r'.evalOutputs M ρ :=
  Silmaril.Proofs.SSA.Peggy.Bridge.Egg.outputs_sound cert M hrules ρ

theorem checkOutputs_sound [DecidableEq Data] (eqPrim : PrimitiveEq P)
    {rs : List (Core.Rule (signature P))} {r : Ranked g} {r' : Ranked g'}
    {receipts : ∀ i : Fin results.length, Core.Replay.Receipt rs (context params) results[i]}
    (accepted : (checkOutputs eqPrim r r' receipts).isSome)
    (M : Interpretation P) (hrules : ∀ rule ∈ rs, rule.Holds (model M)) (ρ : M.Inputs params) :
    r.evalOutputs M ρ = r'.evalOutputs M ρ :=
  outputs_sound ((checkOutputs eqPrim r r' receipts).get accepted).down M hrules ρ

end Silmaril.SSA.Peggy.Bridge.Egg
