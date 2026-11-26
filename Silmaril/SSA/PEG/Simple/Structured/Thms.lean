module

public import Silmaril.SSA.PEG.Simple.Structured.Defs
public import Silmaril.SSA.PEG.Semantics.Thms
import Silmaril.Proofs.SSA.PEG.Simple.Structured.Correctness
import Silmaril.Proofs.SSA.PEG.Simple.Structured.Structural

public section

namespace Silmaril.SSA.PEG.Simple.Structured

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params : List (Ty Data)} {t : Ty Data}

/-- Admission covers all Figure 11 requests, including arbitrary samples in
an inner loop with fixed enclosing coordinates. -/
theorem translate_rank (p : Program P true params t) (neg : P [.bool] .bool) :
    (rank (program p neg).nodes.length).check (translate p neg) = true :=
  Proofs.rankChecked (program p neg).code (program p neg).refs

theorem translate_forest (p : Program P true params t) (neg : P [.bool] .bool) :
    (translate p neg).forest.WellFormed :=
  Proofs.forestWellFormed (program p neg).code (program p neg).refs

/-- The loop ID is its own pass row's address. Distinct pass rows
therefore label distinct loops. -/
theorem translate_pass_id (p : Program P true params t) (neg : P [.bool] .bool)
    (row l : Fin (program p neg).nodes.length)
    (h : passLoop ((translate p neg).node row).label = some l) : l = row :=
  Proofs.passAtOwnId (program p neg).code (program p neg).refs row l h

theorem translate_feedbackCycles (p : Program P true params t) (neg : P [.bool] .bool) :
    (translate p neg).FeedbackCycles :=
  Proofs.feedbackCycles (program p neg).code (program p neg).refs

/-- Compiler output satisfies the structural admission used by Peggy.
A dependency enters a hidden loop through a sample, and a cycle through a
pass or eval crosses feedback of a strictly enclosing loop. -/
theorem translate_wellFormed (p : Program P true params t) (neg : P [.bool] .bool) :
    (translate p neg).WellFormed :=
  Proofs.structuralWellFormed p neg

theorem translate_demandWellFounded (p : Program P true params t) (neg : P [.bool] .bool) :
    WellFounded (translate p neg).Demand :=
  (translate p neg).demandWellFounded (translate_wellFormed p neg)

/-- Theorem 2 for the full typed SIMPLE statement syntax. An actual successful
execution gives a defined PEG return. Each loop's first exit and eval prefix
come from its finite source trace, at the enclosing iteration coordinates. -/
theorem translate_returns (p : Program P true params t) (neg : P [.bool] .bool)
    (m : Interpretation.{u,v,w} P) (env : Tuple m.Value params)
    (negSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    {value : m.Value t} (run : p.Returns m env value) (i : Index (program p neg).nodes.length) :
    (translate p neg).observe m
      ((translate p neg).denote m env (translate_demandWellFounded p neg)) i = .cons (some value) .nil :=
  Proofs.programReturns p neg m env negSem run ((translate p neg).denote_solves m env _) i

end Silmaril.SSA.PEG.Simple.Structured
