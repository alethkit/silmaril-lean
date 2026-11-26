module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseAndUnaryReturns.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.PairSequencing.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.ReturnJoin

/-! # An instruction-free pair still requires a constructor sequencing equation -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction.PairSequencing

open Silmaril Silmaril.Isotope.LambdaSSA
open scoped Paper.BoundSimulation.Obstruction
open Paper.UnaryReturn.Beta.Constructors (pairSequence)
open Paper.UnaryReturn.Beta.Constructors.Example (source)
open Paper.RetainedLet (returnOnce)

open Paper.Extension.Singleton (ofRegion pairArrows)
open CfgEta.TypeCategory (returnRegion_typed)

local instance : HasEff Empty Bool := ⟨Empty.elim⟩

local notation "Join" => Paper.WithCaseAndUnaryReturns.JoinedStep (τ := Ty Empty) (Φ := Empty) false

/-- A unary let inside the left component cannot be sequenced by the
projection, unit, pure case and unary forwarding return equations. -/
theorem case_unary_pair_sequence_fails :
    ¬ Paper.Extension.Eqv Join [source]
      (returnOnce (.pair (.let₁ (.var 0) (.var 0)) (.var 0)))
      (pairSequence (.let₁ (.var 0) (.var 0)) (.var 0)) [product source source] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.case_unary_pair_sequence_fails

/-- The same separation prevents sequential pairing of the operand returns
from decomposing this singleton arrow. -/
theorem case_unary_returnPair_ne_pairArrows
    (ha : Tm.HasType [source] (.let₁ (.var 0) (.var 0) : Tm Empty) source)
    (hb : Tm.HasType [source] (.var 0 : Tm Empty) source) :
    ofRegion Join (returnRegion_typed (.pair ha hb)) ≠
      pairArrows Join (ofRegion Join (returnRegion_typed ha)) (ofRegion Join (returnRegion_typed hb)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.case_unary_returnPair_ne_pairArrows ha hb

end Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction.PairSequencing
