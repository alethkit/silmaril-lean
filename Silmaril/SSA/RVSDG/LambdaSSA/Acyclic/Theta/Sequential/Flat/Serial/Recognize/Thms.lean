module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Recognize.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Recognize.Complete

/-! # Certified recovery from numbered serial graphs -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Recognize

open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open Isotope.LetIter.ProofRelevant.Semantics

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A X Y L E D : τ}
variable {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

variable [DecidableEq τ] [DecidableEq Φ]
variable {g : Graph Φ A X Y L E D sigs}

omit [DecidableEq Φ] in
theorem candidate_generated (s : Spine Φ A X Y L E D sigs) (h : LeftAssociated s) :
    candidate s.graph = some s :=
  Proofs.candidate_generated s h

/-- For the emitted left-associated layout and the supported local body
grammar, recognition recovers the original typed spine. -/
theorem complete (s : Spine Φ A X Y L E D sigs) (h : LeftAssociated s) :
    recognize s.graph = some s.decomposition :=
  Proofs.complete s h

theorem reject_wiring (s : Spine Φ A X Y L E D sigs) (parsed : candidate g = some s)
    (different : s.graph ≠ g) : recognize g = none := by
  rw [recognize, parsed, Option.bind_some]
  cases s with
  | loop s => simp only [certify, dite_eq_right different]
  | link p q => simp only [certify, rejectCut different, Option.map_none]

variable {ε σ : Type u} [HasEff Φ ε] [Bot ε] [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
  [InstructionModel Φ τ ε (StateT σ Part.{u})]

/-- Every successful match carries a certificate for this actual graph
and for the actual flat CFG recovered from it. -/
theorem sound {d : Decomposition g} (_accepted : recognize g = some d)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) :
    Agrees (ε := ε) (σ := σ) d.recover g :=
  d.agrees coherent

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Recognize
