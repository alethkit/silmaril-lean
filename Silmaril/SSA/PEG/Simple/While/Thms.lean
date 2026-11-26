module

public import Silmaril.SSA.PEG.Simple.While.Trace
public import Silmaril.SSA.PEG.Semantics.Thms
import Silmaril.Proofs.SSA.PEG.Simple.While.Guard
import Silmaril.Proofs.SSA.PEG.Simple.While.Returns

public section

namespace Silmaril.SSA.PEG.Simple

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params : List (Ty Data)} {out : Ty Data}

theorem Exec.while_trace {m : Interpretation.{u,v,w} P} {guard : Expr P params .bool}
    {body : Stmt P true params params} {input final : Tuple m.Value params}
    (run : Exec m (.while rfl guard body) input (some final)) :
    ∃ k, WhileTrace m guard body k input final :=
  WhileProofs.whileTrace run

/-- The compiler's rank is checked for every emitted graph. In particular it
admits eval and pass demands at arbitrary iterations. -/
theorem WhileProgram.translate_rank (p : WhileProgram P params out) (neg : P [.bool] .bool) :
    p.rank.check (p.translate neg) = true :=
  WhileProofs.checkRank p neg

/-- No cycle crosses a sampling or index edge, and every nonempty cycle
contains feedback. There is one loop and every loop reference is in scope. -/
theorem WhileProgram.translate_wellFormed (p : WhileProgram P params out) (neg : P [.bool] .bool) :
    (p.translate neg).WellFormed :=
  WhileProofs.wellFormed p neg

theorem WhileProgram.translate_demandWellFounded (p : WhileProgram P params out) (neg : P [.bool] .bool) :
    WellFounded (p.translate neg).Demand :=
  (p.translate neg).demandWellFounded_of_check p.rank (p.translate_rank neg)

/-- A successful source run of the top-level while returns the same value
in the compiled PEG. The supplied primitive must implement Boolean negation.
The source run gives the entire defined prefix demanded by pass and eval. -/
theorem WhileProgram.translate_returns (p : WhileProgram P params out) (neg : P [.bool] .bool)
    (m : Interpretation.{u,v,w} P) (input : Tuple m.Value params)
    (notSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    {value : m.Value out} (run : p.source.Returns m input value) (i : Index 1) :
    (p.translate neg).observe m
      ((p.translate neg).denote m input (p.translate_demandWellFounded neg)) i =
      .cons (some value) .nil :=
  WhileProofs.returns p neg m input notSem run ((p.translate neg).denote_solves m input _) i

end Silmaril.SSA.PEG.Simple
