module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Model.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Observations.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.Reverse.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Reverse.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Agreement

/-! # Exact state agreement with the actual flat linked CFG -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open OrderedTheta (carriedData)
open NestedTheta.ExplicitRuntime (EntryChecked)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A I B K M C J E D : τ}

noncomputable def canonical (p : Conditional.Guarded Φ A I B K M M) (q : Loop Φ M C J E D) :
    Decomposition (compile p q) B K C J :=
  ⟨Conditional.Wiring.code p, ExplicitRuntime.Wiring.loop q,
    Conditional.Reverse.canonical p, ExplicitRuntime.Reverse.canonical q, rfl⟩

theorem recover_canonical (p : Conditional.Guarded Φ A I B K M M) (q : Loop Φ M C J E D) :
    (canonical p q).recover = Source p q := by
  change Source (Conditional.Reverse.canonical p).view.decode (ExplicitRuntime.Reverse.canonical q).view.decode = _
  rw [Conditional.Reverse.canonical_decode, ExplicitRuntime.Reverse.canonical_decode]

theorem compile_checked (p : Conditional.Guarded Φ A I B K M M) (q : Loop Φ M C J E D) :
    Nonempty (EntryChecked (a := carriedData A) (b := carriedData (Wires.Second M E D)) (compile p q).toTerm) :=
  ⟨joinChecked (Conditional.Wiring.code p) (ExplicitRuntime.Wiring.loop q)⟩

variable {ε σ : Type u} [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]

/-- With a producer return in hand, the observable remainder is exactly
the consumer graph run on its payload and token. -/
theorem compile_after (p : Conditional.Guarded Φ A I B K M M) (q : Loop Φ M C J E D)
    (input : TyDen A) (initial token : σ) (mid : LabelDen [M,M])
    (finished : Conditional.returns (ε := ε) (Conditional.graph p) input initial mid token) :
    observe (ε := ε) (compile p q) input initial =
      ExplicitRuntime.observe (ε := ε) (ExplicitRuntime.graph q) (merge mid) token :=
  Proofs.compile_after p q input initial token mid finished

theorem compile_no_producer (p : Conditional.Guarded Φ A I B K M M) (q : Loop Φ M C J E D)
    (input : TyDen A) (initial : σ)
    (absent : Conditional.observe (ε := ε) (Conditional.graph p) input initial = Part.none) :
    observe (ε := ε) (compile p q) input initial = Part.none :=
  Proofs.compile_no_producer p q input initial absent

theorem compile_observe (p : Conditional.Guarded Φ A I B K M M) (q : Loop Φ M C J E D)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) (compile p q) env.2 initial = Part.map (ExplicitRuntime.exitTuple (A := M))
      ((Region.denote (ε := ε) (m := StateT σ Part.{u}) (Source p q).typing env).run initial) :=
  Proofs.compile_observe p q coherent env initial

theorem compile_returns_iff (p : Conditional.Guarded Φ A I B K M M) (q : Loop Φ M C J E D)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (exit : LabelDen [E,D]) (initial final : σ) :
    returns (ε := ε) (compile p q) env.2 initial exit final ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) (Source p q).typing env).run initial =
        Part.some (exit, final) :=
  Proofs.returns_of_observe _ _ initial final exit _ (compile_observe p q coherent env initial)

variable {g : Graph Φ A I M E D}

theorem Decomposition.region_observe (w : Decomposition g B K C J)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.map (ExplicitRuntime.exitTuple (A := M))
      ((Region.denote (ε := ε) (m := StateT σ Part.{u}) w.recover.typing env).run initial) :=
  Proofs.recovered_observe w coherent env initial

theorem Decomposition.region_returns_iff (w : Decomposition g B K C J)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (exit : LabelDen [E,D]) (initial final : σ) :
    returns (ε := ε) g env.2 initial exit final ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.recover.typing env).run initial = Part.some (exit, final) :=
  Proofs.returns_of_observe _ _ initial final exit _ (w.region_observe coherent env initial)

/-- A supplied joint decomposition transports finite returns between
the actual numbered splice and the two checked numbered components. -/
theorem Decomposition.returns_iff_components (w : Decomposition g B K C J)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (exit : LabelDen [E,D]) (initial final : σ) :
    returns (ε := ε) g env.2 initial exit final ↔
      ∃ (mid : LabelDen [M,M]) (token : σ),
        Conditional.returns (ε := ε) w.producer.1.toGraph env.2 initial mid token ∧
        ExplicitRuntime.returns (ε := ε) w.consumer.1.toGraph (merge mid) token exit final :=
  (w.region_returns_iff coherent env exit initial final).trans
    (Flat.recover_returns_iff w.first w.second coherent env exit initial final)

theorem Decomposition.region_undefined_iff (w : Decomposition g B K C J)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.none ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.recover.typing env).run initial = Part.none := by
  rw [w.region_observe coherent env initial]
  exact Proofs.map_none_iff _ _

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered
