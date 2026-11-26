module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Reverse.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Reverse.Complete
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Reverse.Scan

/-! # Completeness at the emitted numbering and soundness of recovered CFGs -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Reverse

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open Sequential.Flat.Serial (observe returns)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ] [DecidableEq τ] [DecidableEq Φ]
variable {A X Z L E D : τ}
variable {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}
variable {g : Sequential.Flat.Serial.Graph Φ A X Z L E D sigs}

open NestedTheta.ExplicitRuntime (Checked EntryChecked)
open NestedTheta.ExplicitRuntime.Splice (Routing relocate append)
open OrderedRuntime.Structured (Data Threaded runtime)

omit [DecidableEq τ] [DecidableEq Φ] in
/-- Relocating a checked continuation changes wire addresses and retains
its local label layout, including all child scopes. -/
theorem scan_relocate {args input outs : Ports (OrderedRuntime.Structured.Ty τ)}
    {past target suffix : List (Ports (OrderedRuntime.Structured.Ty τ))}
    {a : Data input} {b : Data outs} {c : Data args} {live : Origin (Threaded input) past runtime}
    {term : NestedTheta.Term (Sequential.Wires.Op Φ) (Threaded input) past suffix (Threaded outs)}
    (route : Routing (Threaded input) past (Threaded args) target)
    (h : Checked (TwoBlock.TwoExit.Pure τ) (Sequential.Wires.Effect Φ) a b live term) :
    scan (relocate (c := c) route h).1 = scan term :=
  Proofs.scan_relocate route h

omit [DecidableEq τ] [DecidableEq Φ] in
/-- The structured layout scanner preserves each side of a checked splice. -/
theorem scan_append {args input outs : Ports (OrderedRuntime.Structured.Ty τ)}
    {past firstSigs tailSigs : List (Ports (OrderedRuntime.Structured.Ty τ))}
    {a : Data args} {b : Data input} {c : Data outs} {live : Origin (Threaded args) past runtime}
    {p : NestedTheta.Term (Sequential.Wires.Op Φ) (Threaded args) past firstSigs (Threaded input)}
    {q : NestedTheta.Term (Sequential.Wires.Op Φ) (Threaded input) [] tailSigs (Threaded outs)}
    (first : Checked (TwoBlock.TwoExit.Pure τ) (Sequential.Wires.Effect Φ) a b live p)
    (tail : EntryChecked (a := b) (b := c) q) :
    scan (append tail first).1 = (do let xs ← scan p; let ys ← scan q; pure (xs ++ ys)) :=
  Proofs.scan_append first tail

omit [DecidableEq τ] [DecidableEq Φ] in
/-- The existing local association convention preserves the checked code. -/
theorem associate_bodies (n : Normal Φ A X Z L E D sigs) :
    ∃ out : Normal Φ A X Z L E D sigs, Supported out ∧ out.toSyntax.code = n.toSyntax.code :=
  Proofs.associate_bodies n

omit [DecidableEq Φ] in
theorem candidate_generated (n : Normal Φ A X Z L E D sigs) (h : Supported n) :
    candidate n.toSyntax.graph = some n :=
  Proofs.candidate_generated n h

theorem reject_wiring (n : Normal Φ A X Z L E D sigs) (parsed : candidate g = some n)
    (different : n.toSyntax.graph ≠ g) : recognize g = none := by
  simp [recognize, parsed, certify, different]

/-- Every emitted normal layout with right-associated local bodies
recovers its original normalized syntax. -/
theorem recognize_generated (n : Normal Φ A X Z L E D sigs) (h : Supported n) :
    recognize n.toSyntax.graph = some ⟨n, rfl⟩ := by
  simp [recognize, candidate_generated n h, certify]

theorem recover_generated (n : Normal Φ A X Z L E D sigs) (h : Supported n) :
    recover n.toSyntax.graph = some ⟨n.toSyntax.source.region, .generated n.toSyntax⟩ := by
  rw [recover, recognize_generated n h]
  rfl

/-- Acceptance characterizes the numbered image of the outer normal form.
Local loop-body association may change in the recovered source. -/
theorem recover_isSome_iff (g : Sequential.Flat.Serial.Graph Φ A X Z L E D sigs) :
    (recover g).isSome = true ↔ ∃ n : Normal Φ A X Z L E D sigs, n.toSyntax.graph = g :=
  Proofs.recover_isSome_iff g

variable {ε σ : Type u} [HasEff Φ ε] [Bot ε] [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
  [InstructionModel Φ τ ε (StateT σ Part.{u})]

/-- A successful recovery compares the actual numbered graph with the
repository denotation of the recovered flat LambdaSSA CFG. -/
theorem recover_observe {w : Fibre g} (_accepted : recover g = some w)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.map (ExplicitRuntime.exitTuple (A := L))
      ((Region.denote (ε := ε) (m := StateT σ Part.{u}) w.2.typing env).run initial) :=
  w.2.region_observe coherent env initial

theorem recover_returns_iff {w : Fibre g} (_accepted : recover g = some w)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (exit : LabelDen [E,D]) (initial final : σ) :
    returns (ε := ε) g env.2 initial exit final ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.2.typing env).run initial = Part.some (exit, final) :=
  w.2.region_returns_iff coherent env exit initial final

theorem recover_undefined_iff {w : Fibre g} (_accepted : recover g = some w)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.none ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.2.typing env).run initial = Part.none :=
  w.2.region_undefined_iff coherent env initial

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Reverse
