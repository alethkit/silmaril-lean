module

public import Silmaril.SSA.Peggy.Bridge.Egg.Defs
import Silmaril.Logic.Egg.Core.Thms

public section

namespace Silmaril.Proofs.SSA.Peggy.Bridge.Egg

open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Egg
open Silmaril.SSA
open Silmaril.SSA.Peggy.Acyclic (Interpretation Ranked)
open Silmaril.SSA.Peggy.Bridge.Egg

variable {Data : Type} {P : PEG.InstructionSet Data}
variable {params results : List (PEG.Ty Data)} {n n' : Nat}
variable {g : PEG.Graph P params results n 0} {g' : PEG.Graph P params results n' 0}

private theorem eval_cast (M : Interpretation P) (ρ : M.Inputs params)
    {s t : PEG.Ty Data} (h : s = t) (a : Term P params s) :
    (h ▸ a : Term P params t).eval (model M) ρ = (h ▸ a.eval (model M) ρ : M.Partial t) := by
  cases h
  rfl

private theorem eval_encodeLabel (M : Interpretation P) (ρ : M.Inputs params)
    {ins out} (label : PEG.Label P params (Fin 0) ins out)
    (args : ∀ j : Fin ins.length, Term P params ins[j]) :
    (encodeLabel label args).eval (model M) ρ =
      M.evalLabel ρ label (fun j => (args j).eval (model M) ρ) := by
  cases label with
  | param p =>
    simp only [encodeLabel, Interpretation.evalLabel, eval_cast, EQ.Term.eval]
    rfl
  | op op => rfl
  | phi => rfl
  | theta l | eval l | pass l => exact l.elim0

theorem encode_eval (r : Ranked g) (M : Interpretation P) (ρ : M.Inputs params) (i : Fin n) :
    (encode r i).eval (model M) ρ = r.eval M ρ i := by
  induction i using (measure r.rank).wf.induction with
  | h i ih =>
    unfold encode Ranked.eval
    rw [Ranked.fold, Ranked.fold, eval_encodeLabel]
    congr 1
    funext j
    rw [eval_cast]
    exact congrArg (fun value => ((g.node i).arg j).typed ▸ value)
      (ih _ (r.decreases i j))

theorem encodeOutputs_eval (r : Ranked g) (M : Interpretation P) (ρ : M.Inputs params)
    (i : Fin results.length) :
    (encodeOutputs r i).eval (model M) ρ = r.evalOutputs M ρ i := by
  simp only [encodeOutputs, Ranked.evalOutputs, eval_cast, encode_eval]
  rfl

theorem outputs_sound {rs : List (Core.Rule (signature P))} {r : Ranked g} {r' : Ranked g'}
    (cert : OutputsExplained rs r r') (M : Interpretation P)
    (hrules : ∀ rule ∈ rs, rule.Holds (model M)) (ρ : M.Inputs params) :
    r.evalOutputs M ρ = r'.evalOutputs M ρ := by
  funext i
  rw [← encodeOutputs_eval r, ← encodeOutputs_eval r']
  exact Core.explanation_sound (model M) ρ hrules (fun _ h => False.elim h) (cert i)

end Silmaril.Proofs.SSA.Peggy.Bridge.Egg
