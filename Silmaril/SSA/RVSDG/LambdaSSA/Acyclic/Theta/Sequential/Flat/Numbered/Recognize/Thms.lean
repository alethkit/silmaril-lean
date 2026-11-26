module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Check.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Thms

/-! # Checked recognition and semantic recovery -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A I M E D : τ} {g : Graph Φ A I M E D}

/-- Recognition certifies the actual input graph's single live token. The
certificate can be used independently of the recovered CFG and model. -/
def Match.checked (m : Match g) :
    NestedTheta.ExplicitRuntime.EntryChecked (a := OrderedTheta.carriedData A)
      (b := OrderedTheta.carriedData (Wires.Second M E D)) g.toTerm :=
  m.wiring ▸ joinChecked (Conditional.Wiring.code m.components.first)
    (ExplicitRuntime.Wiring.loop m.components.second)

/-- Accepted graphs have the existing source-free joint decomposition. -/
noncomputable def Match.decomposition (m : Match g) :
    Decomposition g m.components.B m.components.K m.components.C m.components.J :=
  Eq.mp (congrArg (fun g => Decomposition g m.components.B m.components.K m.components.C m.components.J) m.wiring)
    (canonical m.components.first m.components.second)

theorem Match.recover_eq (m : Match g) : m.decomposition.recover = m.recover := by
  obtain ⟨components, wiring⟩ := m
  subst g
  exact recover_canonical components.first components.second

section Recognition

variable [DecidableEq τ] [DecidableEq Φ]

/-- Whenever the deterministic label parse reconstructs the actual typed
wiring, certification accepts that candidate. -/
theorem complete (components : Components Φ A I M E D) (parsed : candidate g = some components)
    (wired : components.graph = g) :
    recognize g = some ⟨components, wired⟩ := by
  simp only [recognize, parsed, Option.bind_some, certify, dite_eq_left wired]

theorem reject_cut (absent : cut g = none) : recognize g = none := by
  simp only [recognize, candidate, absent]
  rfl

theorem reject_wiring (components : Components Φ A I M E D) (parsed : candidate g = some components)
    (different : components.graph ≠ g) : recognize g = none := by
  simp only [recognize, parsed, Option.bind_some, certify, dite_eq_right different]

end Recognition

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)

variable {ε σ : Type u} [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]

theorem Match.region_returns_iff (m : Match g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (exit : LabelDen [E,D]) (initial final : σ) :
    returns (ε := ε) g env.2 initial exit final ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) m.recover.typing env).run initial = Part.some (exit, final) := by
  simpa only [m.recover_eq] using m.decomposition.region_returns_iff coherent env exit initial final

theorem Match.region_undefined_iff (m : Match g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.none ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) m.recover.typing env).run initial = Part.none := by
  simpa only [m.recover_eq] using m.decomposition.region_undefined_iff coherent env initial

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize
