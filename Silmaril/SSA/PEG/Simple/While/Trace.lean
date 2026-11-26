module

public import Silmaril.SSA.PEG.Simple.While.Defs

public section

namespace Silmaril.SSA.PEG.Simple

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data} {vars : List (Ty Data)}

/-- A finite successful while run with its exact number of body steps. -/
inductive WhileTrace (m : Interpretation.{u,v,w} P) (guard : Expr P vars .bool)
    (body : Stmt P true vars vars) :
    Nat → Tuple m.Value vars → Tuple m.Value vars → Prop where
  | stop {store} (test : guard.eval m store = some ⟨false⟩) : WhileTrace m guard body 0 store store
  | step {k start next final} (test : guard.eval m start = some ⟨true⟩)
      (run : Exec m body start (some next)) (rest : WhileTrace m guard body k next final) :
      WhileTrace m guard body (k + 1) start final

variable {out : Ty Data}

/-- Purity comes from the interpretation. Both the guard and each complete
body step must return on every defined carried store. -/
structure WhileProgram.Total (p : WhileProgram P vars out) (m : Interpretation.{u,v,w} P) : Prop where
  guard : ∀ store : Tuple m.Value vars, ∃ b : Bool, p.guard.eval m store = some ⟨b⟩
  body : ∀ store : Tuple m.Value vars, ∃ next, Exec m p.body.enableWhile store (some next)

/-- Evidence recovered from a defined eval root. The finite trace stops at
the pass index, and the selected θ is defined throughout eval's prefix. -/
structure WhileProgram.ExitWitness (p : WhileProgram P vars out) (neg : P [.bool] .bool)
    (m : Interpretation.{u,v,w} P) (input : Tuple m.Value vars)
    (values : (p.translate neg).Valuation m) (idx : Index 1)
    (k : Nat) (final : Tuple m.Value vars) (value : m.Value out) : Prop where
  trace : WhileTrace m p.guard p.body.enableWhile k input final
  returned : final.get p.retvar = value
  pass : p.readPort neg m values p.passPort idx = some ⟨k⟩
  sample : p.readPort neg m values (p.carriedPort p.retvar) (fun _ => k) = some value
  definedBefore : ∀ j < k, (p.readPort neg m values (p.carriedPort p.retvar) (fun _ => j)).isSome

end Silmaril.SSA.PEG.Simple
