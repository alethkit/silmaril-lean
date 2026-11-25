module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Model.Defs
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Region

/-! # The actual flat CFG denotes two successive loop computations -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open Silmaril.Elgot (Iterate LawfulElgotMonad)

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {m : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m]
variable {A B K M C J E D : τ}

/-- The only inter-loop edges enter the second header. The flat iteration
therefore factors through the actual denotations of the two constituent CFGs. -/
theorem region_sequential (s : Loops Φ A B K M C J E D)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (regionTyping s) env =
      Region.denote (ε := ε) (m := m) (Theta.regionTyping s.first) env >>= fun mid =>
        Region.denote (ε := ε) (m := m) (Theta.regionTyping s.second) (PUnit.unit, merge mid) :=
  Proofs.region_sequential s coherent env

omit [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m] [InstructionModel Φ τ ε m] in
/-- Splitting the local label table recovers an external label and its payload. -/
theorem split_external (external locals : List τ) (i : Nat) {Z : τ}
    (outside : Isotope.SSA.At (locals ++ external) (i + locals.length) Z)
    (inside : Isotope.SSA.At external i Z) (x : TyDen Z) :
    LabelValue.appendSplit locals external (LabelValue.inject (i + locals.length) outside x) =
      .inl (LabelValue.inject i inside x) :=
  Proofs.split_external external locals i outside inside x

/-- A typed entry may return straight to an external label or start an
existing flat loop. Its block table ignores the retained entry environment. -/
theorem region_entry (s : Loop Φ A B K E D) {Γ : List τ} {gate : Isotope.LambdaSSA.Region Φ}
    (typing : Isotope.LambdaSSA.Region.HasType Γ gate (Theta.Labels s))
    {action : Env Γ → m (LabelDen (Theta.Labels s))}
    (entryDenotes : RegionDenotes (m := m) ε typing action)
    (choose : Env Γ → m (LabelDen [E,D] ⊕ TyDen A))
    (entrySplit : ∀ env, (action env >>= fun x => pure (LabelValue.appendSplit _ _ x)) =
      (choose env >>= fun branch => pure (splitEntry s branch)))
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env Γ) :
    Region.denote (ε := ε) (m := m) (.cfg (Theta.localTypes s) typing
      (fun i => (Theta.blockAt s i).typing Γ)) env =
      choose env >>= fun
        | .inl external => pure external
        | .inr header => Region.denote (ε := ε) (m := m) (Theta.regionTyping s) (PUnit.unit, header) :=
  Proofs.region_entry s typing entryDenotes choose entrySplit coherent env

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential
