module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Recognize.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Recognize.Complete
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Recognize.Scan

/-! # Certified recovery from numbered serial graphs -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Recognize

open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open Isotope.LetIter.ProofRelevant.Semantics

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A X Y L E D : τ}
variable {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

open OrderedRuntime.Structured (Data Threaded runtime)
open NestedTheta.ExplicitRuntime (Checked EntryChecked)
open NestedTheta.ExplicitRuntime.Splice (append)

/-- Scanning a checked splice appends the two local mark lists. The splice
changes wire origins while retaining the nested regions and their bounds. -/
theorem scan_append {args middle outs : Ports (OrderedRuntime.Structured.Ty τ)}
    {past after : List (Ports (OrderedRuntime.Structured.Ty τ))}
    {a : Data args} {b : Data middle} {c : Data outs}
    {live : Origin (Threaded args) past runtime}
    {p : NestedTheta.Term (Wires.Op Φ) (Threaded args) past sigs (Threaded middle)}
    {q : NestedTheta.Term (Wires.Op Φ) (Threaded middle) [] after (Threaded outs)}
    (first : Checked (TwoBlock.TwoExit.Pure τ) (Wires.Effect Φ) a b live p)
    (next : EntryChecked (a := b) (b := c) q) :
    scan (append next first).1 = (do let xs ← scan p; let ys ← scan q; pure (xs ++ ys)) :=
  Proofs.scan_append first next

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
