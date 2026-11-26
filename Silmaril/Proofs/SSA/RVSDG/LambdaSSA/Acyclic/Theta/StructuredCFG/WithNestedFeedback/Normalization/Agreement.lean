module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Normalization.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Normalization.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Recursive.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Normalization.Proofs

open Reverse.Recursive (Normal)
open Sequential
open Isotope.LambdaSSA (Region)
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open Silmaril.Elgot

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A X Z H M I J L E D : τ}
variable {ps qs sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

private theorem source_ofStructured (n : StructuredCFG.Reverse.Normal Φ A X Z L E D sigs) :
    (ofStructured n).toSyntax.source = n.toSyntax.source := by
  induction n <;>
    simp [ofStructured, Normal.toSyntax, Reverse.Recursive.LeafView.toSyntax,
      StructuredCFG.Reverse.Normal.toSyntax, Syntax.source, StructuredCFG.Syntax.source, *]

variable {ε : Type u} [HasEff Φ ε] [Bot ε] [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {m : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m]

theorem denote_append (p : Normal Φ A X Z H M M ps) (q : Normal Φ M I J L E D qs)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (append p q).toSyntax.source.typing env =
      Region.denote (ε := ε) (m := m) p.toSyntax.source.typing env >>= fun out =>
        Region.denote (ε := ε) (m := m) q.toSyntax.source.typing (PUnit.unit, merge out) := by
  induction p, q using append.induct with
  | case1 _ tail first =>
    rw [append]
    exact Flat.denote_link first.toSyntax.source tail.toSyntax.source coherent env
  | case2 _ _ _ _ _ tail first rest ih
  | case3 _ _ _ _ _ tail first rest ih
  | case4 _ _ _ _ _ _ _ _ _ left right tail gate rest ih =>
    rw [append]
    simp only [Normal.toSyntax, Syntax.source, Flat.denote_link _ _ coherent, bind_assoc]
    congr 1
    funext out
    exact ih (PUnit.unit, merge out)

theorem denote_normalize (s : Syntax Φ A X Z L E D sigs)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (normalize s).toSyntax.source.typing env =
      Region.denote (ε := ε) (m := m) s.source.typing env := by
  induction s with
  | structured p =>
    simp only [normalize, source_ofStructured, Syntax.source]
    exact StructuredCFG.Normalization.denote_normalize p coherent env
  | nested => rfl
  | link p q hp hq =>
    rw [normalize, denote_append _ _ coherent, hp env]
    change _ = Region.denote (ε := ε) (m := m) (Flat.link p.source q.source).typing env
    rw [Flat.denote_link _ _ coherent]
    congr 1
    funext out
    exact hq (PUnit.unit, merge out)
  | branch gate p q k hp hq hk =>
    simp only [normalize, Normal.toSyntax, Syntax.source, Flat.denote_link _ _ coherent, hk]
    congr 1
    simp only [Flat.denote_fork _ _ _ coherent, hp, hq]

section PartialState

variable {σ : Type u} [InstructionModel Φ τ ε (StateT σ Part.{u})]

theorem compile_observe (s : Syntax Φ A X Z L E D sigs)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    Flat.Serial.observe (ε := ε) (compile s) env.2 initial = Part.map (ExplicitRuntime.exitTuple (A := L))
      ((Region.denote (ε := ε) (m := StateT σ Part.{u}) s.source.typing env).run initial) := by
  rw [← denote_normalize s coherent env]
  exact (Related.generated (normalize s).toSyntax).region_observe coherent env initial

private theorem map_injective {P Q : Type u} {f : P → Q} (hf : Function.Injective f) :
    Function.Injective (Part.map f) := by
  intro x y same
  apply Part.ext
  intro a
  have member := Iff.of_eq (congrArg (fun p : Part Q => f a ∈ p) same)
  simpa only [Part.mem_map_iff, hf.eq_iff, exists_eq_right] using member

variable [DecidableEq τ] [DecidableEq Φ]

theorem recover_denote (s : Syntax Φ A X Z L E D sigs)
    {w : Fibre (compile s)} (accepted : Reverse.Recursive.recover (compile s) = some w)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.2.typing env).run initial =
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) s.source.typing env).run initial := by
  apply map_injective (ExplicitRuntime.exitTuple_injective (A := L))
  exact (Reverse.Recursive.recover_observe accepted coherent env initial).symm.trans
    (compile_observe s coherent env initial)

end PartialState

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Normalization.Proofs
