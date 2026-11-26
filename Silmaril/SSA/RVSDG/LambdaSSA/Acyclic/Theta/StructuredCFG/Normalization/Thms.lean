module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Normalization.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Reverse.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Normalization.Agreement

/-! # The normal compiler preserves the original flat region denotation -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Normalization

open Reverse (Normal)
open Sequential
open Isotope.LambdaSSA (Region)
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open Silmaril.Elgot

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A X Z H M I J L E D : τ}
variable {ps qs sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

theorem normalize_toSyntax (n : Normal Φ A X Z L E D sigs) : normalize n.toSyntax = n := by
  induction n <;> simp [Normal.toSyntax, normalize, append, *]

/-- Every structured source emits a graph accepted by the reverse compiler. -/
theorem compile_recover [DecidableEq τ] [DecidableEq Φ] (s : Syntax Φ A X Z L E D sigs) :
    (Reverse.recover (compile s)).isSome = true :=
  (Reverse.recover_isSome_iff (compile s)).mpr ⟨normalize s, rfl⟩

variable {ε : Type u} [HasEff Φ ε] [Bot ε] [Isotope.Subtyping τ] [TypeModel.{u,u} τ]

section Elgot

variable {m : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m]

/-- Appending into a fork's continuation preserves the selected arm and
executes the shared suffix after its original continuation returns. -/
theorem denote_append (p : Normal Φ A X Z H M M ps) (q : Normal Φ M I J L E D qs)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (append p q).toSyntax.source.typing env =
      Region.denote (ε := ε) (m := m) p.toSyntax.source.typing env >>= fun out =>
        Region.denote (ε := ε) (m := m) q.toSyntax.source.typing (PUnit.unit, merge out) :=
  Proofs.denote_append p q coherent env

/-- Normalization preserves the actual flat region denotation in every
coherent model of the monadic Elgot interface. -/
theorem denote_normalize (s : Syntax Φ A X Z L E D sigs)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (normalize s).toSyntax.source.typing env =
      Region.denote (ε := ε) (m := m) s.source.typing env :=
  Proofs.denote_normalize s coherent env

end Elgot

variable {σ : Type u} [InstructionModel Φ τ ε (StateT σ Part.{u})]

theorem compile_observe (s : Syntax Φ A X Z L E D sigs)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    Flat.Serial.observe (ε := ε) (compile s) env.2 initial = Part.map (ExplicitRuntime.exitTuple (A := L))
      ((Region.denote (ε := ε) (m := StateT σ Part.{u}) s.source.typing env).run initial) :=
  Proofs.compile_observe s coherent env initial

theorem compile_returns_iff (s : Syntax Φ A X Z L E D sigs)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (exit : LabelDen [E,D]) (initial final : σ) :
    Flat.Serial.returns (ε := ε) (compile s) env.2 initial exit final ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) s.source.typing env).run initial =
        Part.some (exit, final) := by
  rw [← denote_normalize s coherent env]
  exact (Related.generated (normalize s).toSyntax).region_returns_iff coherent env exit initial final

theorem compile_undefined_iff (s : Syntax Φ A X Z L E D sigs)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    Flat.Serial.observe (ε := ε) (compile s) env.2 initial = Part.none ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) s.source.typing env).run initial = Part.none := by
  rw [← denote_normalize s coherent env]
  exact (Related.generated (normalize s).toSyntax).region_undefined_iff coherent env initial

/-- The round trip through a normal graph preserves the original CFG's
partial denotation with its typed exit and exact final token. -/
theorem recover_denote [DecidableEq τ] [DecidableEq Φ] (s : Syntax Φ A X Z L E D sigs)
    {w : Reverse.Fibre (compile s)} (accepted : Reverse.recover (compile s) = some w)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.2.typing env).run initial =
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) s.source.typing env).run initial :=
  Proofs.recover_denote s accepted coherent env initial

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Normalization
