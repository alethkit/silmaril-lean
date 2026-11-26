module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Agreement

/-! # Agreement for mixed structured CFGs and their checked reverse fibres -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback

open Sequential
open Sequential.Flat.Serial (Agrees observe returns)
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open Silmaril.Elgot (iter)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A B K M X Z L E D : τ}
variable {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

/-- Every successful leaf observation uses the first external label. -/
theorem Leaf.source_rounds (s : NestedFeedback.Loop Φ A B K M)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) (env : Env [A]) :
    Region.denote (ε := ε) (m := StateT σ Part.{u}) (Leaf.source s).typing env =
      iter (NestedFeedback.round (ε := ε) s) env.2 >>= fun r => pure (Sum.inl r) :=
  Proofs.source_rounds s coherent env

theorem Leaf.agrees (s : NestedFeedback.Loop Φ A B K M)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) :
    Agrees (ε := ε) (σ := σ) (Leaf.source s) (Leaf.code s).1.toGraph :=
  Proofs.leaf_agrees s coherent

theorem Syntax.agrees (s : Syntax Φ A X Z L E D sigs)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) :
    Agrees (ε := ε) (σ := σ) s.source s.graph :=
  Proofs.agrees s coherent

variable {r : Isotope.LambdaSSA.Region Φ} {g : Flat.Serial.Graph Φ A X Z L E D sigs}

theorem Related.region_observe (w : Related A X Z L E D sigs r g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.map (ExplicitRuntime.exitTuple (A := L))
      ((Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial) := by
  cases w with | generated s => exact s.agrees coherent env initial

theorem Related.region_returns_iff (w : Related A X Z L E D sigs r g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (exit : LabelDen [E,D]) (initial final : σ) :
    returns (ε := ε) g env.2 initial exit final ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial = Part.some (exit, final) := by
  cases w with | generated s => exact Proofs.returns_iff (s.agrees coherent) env exit initial final

theorem Related.region_undefined_iff (w : Related A X Z L E D sigs r g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.none ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial = Part.none := by
  rw [w.region_observe coherent env initial, Part.eq_none_iff', Part.eq_none_iff']
  rfl

section Recovery

variable {I J : τ} {qs : List (Ports (OrderedRuntime.Structured.Ty τ))}
variable [DecidableEq τ] [DecidableEq Φ]
variable {left : NestedFeedback.Graph Φ A M} {right : Flat.Serial.Graph Φ M I J L E D qs}
variable {joint : Flat.Serial.Graph Φ A M M L E D (Flat.Serial.Joined M I J (Leaf.Sigs A M) qs)}

omit [Isotope.Subtyping τ] [TypeModel τ] in
theorem recoverLink_of_matches {p : NestedFeedback.Reverse.Match left} {q : StructuredCFG.Reverse.Match right}
    (parsedLeft : NestedFeedback.Reverse.recognize left = some p)
    (parsedRight : StructuredCFG.Reverse.recognize right = some q)
    (cut : Flat.Serial.Cut (ofNested p).code q.decomposition.shape.code joint) :
    recoverLink left right joint = some (linkMatches p q.decomposition cut) := by
  simp [recoverLink, parsedLeft, parsedRight, cut.certified]

end Recovery

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback
