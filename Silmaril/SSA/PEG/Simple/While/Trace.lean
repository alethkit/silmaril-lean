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

end Silmaril.SSA.PEG.Simple
