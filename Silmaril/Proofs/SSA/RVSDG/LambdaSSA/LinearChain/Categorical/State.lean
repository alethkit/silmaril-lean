module

public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.State.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Wires.Thms
import Silmaril.Semantics.Categories.Freyd.CentralUnit.Thms

/-! # Specializing the categorical result to the checked ordered state wire -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.Proofs

open CategoryTheory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
  (RegionTypingCoherent ofMonadicTypeModel ofMonadicInstructionModel)

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A B E D : τ} {tail : List τ}
variable {r : Isotope.LambdaSSA.Region Φ} {g : Loop Φ A E D}

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem denoteState_eq (rel : Related A B E D tail r g)
    (coherent : Agreement.RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Monadic.Env [A]) :
    denoteState (ε := ε) rel.instructions env =
      Monadic.Region.denote (ε := ε) (m := StateT σ Part.{u}) rel.typing env >>= fun label =>
        pure (Monadic.LabelValue.categoricalEquiv [E,D] label) := by
  let J := typeJ (m := StateT σ Part.{u})
  let T := ofMonadicTypeModel (τ := τ)
  let _ := ofMonadicInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})
  let _ : RegionTypingCoherent (Φ := Φ) J T := coherent
  have h := denoteRegion_eq J T rel
  have k := Agreement.categoricalRegionDenote_eq coherent rel.typing env
  rw [Agreement.categoricalRegionDenote, h] at k
  exact k

theorem state_returns (rel : Related A B E D tail r g)
    (coherent : Agreement.RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Monadic.Env [A]) (label : Monadic.LabelDen [E,D]) (initial final : σ) :
    (denoteState (ε := ε) rel.instructions env).run initial =
      Part.some (Monadic.LabelValue.categoricalEquiv [E,D] label, final) ↔
      returns (ε := ε) g env.2 initial label final := by
  rw [denoteState_eq rel coherent, ← rel.region_returns_iff coherent env label initial final]
  let decode := Monadic.LabelValue.categoricalEquiv (τ := τ) [E,D]
  let f : Monadic.LabelDen [E,D] × σ → Monadic.CategoricalLabelDen [E,D] × σ :=
    Prod.map decode id
  have h : Function.Injective f := by
    intro a b same
    apply Prod.ext
    · exact decode.injective (congrArg Prod.fst same)
    · exact congrArg (fun x : Monadic.CategoricalLabelDen [E,D] × σ => x.2) same
  simp only [StateT.run_bind, StateT.run_pure, Part.bind_eq_bind, Part.pure_eq_some]
  change ((Monadic.Region.denote (ε := ε) (m := StateT σ Part.{u}) rel.typing env).run initial).bind
    (fun x => Part.some (f x)) = Part.some (f (label, final)) ↔ _
  rw [Part.bind_some_eq_map, Part.eq_some_iff, Part.mem_map_iff, Part.eq_some_iff]
  exact ⟨fun ⟨x, hx, e⟩ => h e ▸ hx, fun hx => ⟨_, hx, rfl⟩⟩

end Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.Proofs
