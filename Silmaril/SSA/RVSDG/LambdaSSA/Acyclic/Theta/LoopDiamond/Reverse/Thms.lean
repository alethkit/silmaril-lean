module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.LoopDiamond.Reverse.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.LoopDiamond.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.LoopDiamond.Reverse.Complete

/-! # Exact recovery and observations of the recovered flat diamond -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.LoopDiamond.Reverse

open Sequential.Flat.Numbered.Recognize (RightAssociated)
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A M Y E D : τ} {g : Graph Φ A M Y E D}

section Recognition

variable [DecidableEq τ] [DecidableEq Φ]

omit [DecidableEq Φ] in
theorem candidate_generated (s : Diamond Φ A M Y E D)
    (left : RightAssociated s.left.body) (right : RightAssociated s.right.body)
    (tail : RightAssociated s.next.body) :
    candidate (graph s) = some s :=
  Proofs.candidate_generated s left right tail

theorem reject_wiring (s : Diamond Φ A M Y E D) (parsed : candidate g = some s)
    (different : graph s ≠ g) : recognize g = none := by
  simp [recognize, parsed, certify, different]

/-- Already right-associated bodies round trip to the original flat source. -/
theorem recover_generated (s : Diamond Φ A M Y E D)
    (left : RightAssociated s.left.body) (right : RightAssociated s.right.body)
    (tail : RightAssociated s.next.body) :
    recover (graph s) = some ⟨(source s).region, .diamond s⟩ := by
  rw [recover, Proofs.recognize_generated s left right tail]
  rfl

/-- Acceptance is complete for every emitted graph at its literal numbering.
Bodies with other associations may recover a right-associated CFG. -/
theorem recover_isSome_iff (g : Graph Φ A M Y E D) :
    (recover g).isSome = true ↔ ∃ s : Diamond Φ A M Y E D, graph s = g :=
  Proofs.recover_isSome_iff g

end Recognition

variable {ε σ : Type u} [HasEff Φ ε] [Bot ε] [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
  [InstructionModel Φ τ ε (StateT σ Part.{u})]

/-- Every returned fibre describes this actual graph and the repository
denotation of its recovered flat CFG. -/
theorem fibre_observe (w : Fibre g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.map (ExplicitRuntime.exitTuple (A := M))
      ((Region.denote (ε := ε) (m := StateT σ Part.{u}) w.2.typing env).run initial) :=
  w.2.region_observe coherent env initial

theorem fibre_returns_iff (w : Fibre g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (exit : LabelDen [E,D]) (initial final : σ) :
    returns (ε := ε) g env.2 initial exit final ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.2.typing env).run initial = Part.some (exit, final) :=
  w.2.region_returns_iff coherent env exit initial final

theorem fibre_undefined_iff (w : Fibre g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.none ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.2.typing env).run initial = Part.none :=
  w.2.region_undefined_iff coherent env initial

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.LoopDiamond.Reverse
