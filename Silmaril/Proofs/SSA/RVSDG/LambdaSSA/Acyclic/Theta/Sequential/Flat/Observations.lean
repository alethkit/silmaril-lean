module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Observations.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Proofs

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A I B K M C J E D : τ}

theorem guarded_loop_returns (p : Conditional.Guarded Φ A I B K M M) (q : Loop Φ M C J E D)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (exit : LabelDen [E,D]) (initial final : σ) :
    (Region.denote (ε := ε) (m := StateT σ Part.{u})
      (link (Fragment.guarded p) (Fragment.loop q)).typing env).run initial = Part.some (exit, final) ↔
      ∃ (mid : LabelDen [M,M]) (token : σ),
        Conditional.returns (ε := ε) (Conditional.graph p) env.2 initial mid token ∧
        ExplicitRuntime.returns (ε := ε) (ExplicitRuntime.graph q) (merge mid) token exit final := by
  have first := (Conditional.Related.guarded p).region_returns_iff (ε := ε) coherent env
  rw [denote_link _ _ coherent, Fragment.guarded_denote, Fragment.loop_denote,
    StateT.run_bind, Part.bind_eq_bind, Part.eq_some_iff, Part.mem_bind_iff]
  constructor
  · rintro ⟨⟨mid, token⟩, hp, hq⟩
    refine ⟨mid, token, (first mid initial token).mpr (Part.eq_some_iff.mpr hp), ?_⟩
    exact ((ExplicitRuntime.Related.loop q).region_returns_iff (ε := ε) coherent
      (PUnit.unit, merge mid) exit token final).mpr (Part.eq_some_iff.mpr hq)
  · rintro ⟨mid, token, hp, hq⟩
    refine ⟨(mid, token), Part.eq_some_iff.mp ((first mid initial token).mp hp), ?_⟩
    exact Part.eq_some_iff.mp (((ExplicitRuntime.Related.loop q).region_returns_iff
      (ε := ε) coherent (PUnit.unit, merge mid) exit token final).mp hq)


variable {g : Conditional.Graph Φ A I M M} {h : ExplicitRuntime.Graph Φ M E D}

theorem recover_returns (first : Conditional.Reverse.Decomposition g B K)
    (second : ExplicitRuntime.Reverse.Decomposition h C J)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (exit : LabelDen [E,D]) (initial final : σ) :
    (Region.denote (ε := ε) (m := StateT σ Part.{u}) (recover first second).typing env).run initial =
        Part.some (exit, final) ↔
      ∃ (mid : LabelDen [M,M]) (token : σ),
        Conditional.returns (ε := ε) g env.2 initial mid token ∧
        ExplicitRuntime.returns (ε := ε) h (merge mid) token exit final := by
  have result := guarded_loop_returns first.view.decode second.view.decode coherent env exit initial final
  rw [first.wiring, second.wiring] at result
  exact result

theorem recover_undefined (first : Conditional.Reverse.Decomposition g B K)
    (second : ExplicitRuntime.Reverse.Decomposition h C J)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    (Region.denote (ε := ε) (m := StateT σ Part.{u}) (recover first second).typing env).run initial = Part.none ↔
      ¬ ∃ (mid : LabelDen [M,M]) (token : σ) (exit : LabelDen [E,D]) (final : σ),
        Conditional.returns (ε := ε) g env.2 initial mid token ∧
        ExplicitRuntime.returns (ε := ε) h (merge mid) token exit final := by
  rw [Part.eq_none_iff]
  constructor
  · rintro absent ⟨mid, token, exit, final, hp, hq⟩
    exact absent (exit, final) (Part.eq_some_iff.mp
      ((recover_returns first second coherent env exit initial final).mpr ⟨mid, token, hp, hq⟩))
  · rintro absent ⟨exit, final⟩ observed
    obtain ⟨mid, token, hp, hq⟩ := (recover_returns first second coherent env exit initial final).mp
      (Part.eq_some_iff.mpr observed)
    exact absent ⟨mid, token, exit, final, hp, hq⟩

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Proofs
