module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Normalization.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Recursive.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Normalization.Agreement

/-! # Mixed structured compiler and decoder round trip -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Normalization

open Reverse.Recursive (Normal)
open Sequential
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open Silmaril.Elgot

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A X Z H M I J L E D : τ}
variable {ps qs sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

/-- Every admitted mixed source emits a graph accepted by the recursive decoder. -/
theorem compile_recover [DecidableEq τ] [DecidableEq Φ] (s : Syntax Φ A X Z L E D sigs) :
    (Reverse.Recursive.recover (compile s)).isSome = true :=
  (Reverse.Recursive.recover_isSome_iff _).mpr ⟨normalize s, rfl⟩

variable {ε : Type u} [HasEff Φ ε] [Bot ε] [Isotope.Subtyping τ] [TypeModel.{u,u} τ]

section Elgot

variable {m : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m]

/-- Appending uses the original typed join and runs the suffix after the
continuation's return. This law uses ordered monadic bind. -/
theorem denote_append (p : Normal Φ A X Z H M M ps) (q : Normal Φ M I J L E D qs)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (append p q).toSyntax.source.typing env =
      Region.denote (ε := ε) (m := m) p.toSyntax.source.typing env >>= fun out =>
        Region.denote (ε := ε) (m := m) q.toSyntax.source.typing (PUnit.unit, merge out) :=
  Proofs.denote_append p q coherent env

/-- The normalized and original flat regions have equal denotations in
every coherent model of the monadic Elgot interface. -/
theorem denote_normalize (s : Syntax Φ A X Z L E D sigs)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (normalize s).toSyntax.source.typing env =
      Region.denote (ε := ε) (m := m) s.source.typing env :=
  Proofs.denote_normalize s coherent env

end Elgot

variable {σ : Type u} [InstructionModel Φ τ ε (StateT σ Part.{u})]

/-- The emitted checked graph and the original flat CFG share their partial
observation with its decoded label, payload and exact state. -/
theorem compile_observe (s : Syntax Φ A X Z L E D sigs)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    Flat.Serial.observe (ε := ε) (compile s) env.2 initial = Part.map (ExplicitRuntime.exitTuple (A := L))
      ((Region.denote (ε := ε) (m := StateT σ Part.{u}) s.source.typing env).run initial) :=
  Proofs.compile_observe s coherent env initial

/-- The recovered flat CFG preserves the entire partial state denotation of
the original, including absence of a finite return. -/
theorem recover_denote [DecidableEq τ] [DecidableEq Φ] (s : Syntax Φ A X Z L E D sigs)
    {w : Fibre (compile s)} (accepted : Reverse.Recursive.recover (compile s) = some w)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.2.typing env).run initial =
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) s.source.typing env).run initial :=
  Proofs.recover_denote s accepted coherent env initial

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Normalization
