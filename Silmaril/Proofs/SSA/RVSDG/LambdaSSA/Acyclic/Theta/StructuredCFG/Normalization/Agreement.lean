module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Normalization.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Fork.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Reverse.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Normalization.Proofs

open Reverse (Normal)
open Sequential
open Isotope.LambdaSSA (Region)
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open Silmaril.Elgot

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {m : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m]
variable {A X Z H M I J L E D C F : τ}
variable {ps qs sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

private theorem denote_append_of (p : Normal Φ A X Z H C F ps) (q : Normal Φ M I J L E D qs)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) :
    ∀ (left : C = M) (right : F = M) (env : Env [A]),
    Region.denote (ε := ε) (m := m) (append
      (Eq.mp (congrArg₂ (fun c f => Normal Φ A X Z H c f ps) left right) p) q).toSyntax.source.typing env =
      Region.denote (ε := ε) (m := m) p.toSyntax.source.typing env >>= fun out =>
        Region.denote (ε := ε) (m := m) q.toSyntax.source.typing
          (PUnit.unit, merge (Eq.mp (congrArg₂ (fun c f => LabelDen [c,f]) left right) out)) := by
  induction p with
  | loop s =>
    intro left right env
    cases left
    cases right
    exact Flat.denote_link _ _ coherent env
  | link first rest ih =>
    intro left right env
    cases left
    cases right
    simp only [Normal.toSyntax, Syntax.source, Flat.denote_link _ _ coherent, bind_assoc]
    congr 1
    funext out
    exact ih rfl rfl (PUnit.unit, merge out)
  | branch gate left right rest ihLeft ihRight ihRest =>
    intro first second env
    cases first
    cases second
    simp only [Normal.toSyntax, Syntax.source, Flat.denote_link _ _ coherent, bind_assoc]
    congr 1
    funext out
    exact ihRest rfl rfl (PUnit.unit, merge out)

theorem denote_append (p : Normal Φ A X Z H M M ps) (q : Normal Φ M I J L E D qs)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (append p q).toSyntax.source.typing env =
      Region.denote (ε := ε) (m := m) p.toSyntax.source.typing env >>= fun out =>
        Region.denote (ε := ε) (m := m) q.toSyntax.source.typing (PUnit.unit, merge out) :=
  denote_append_of p q coherent rfl rfl env

theorem denote_normalize (s : Syntax Φ A X Z L E D sigs)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (normalize s).toSyntax.source.typing env =
      Region.denote (ε := ε) (m := m) s.source.typing env := by
  induction s with
  | loop => rfl
  | link p q hp hq =>
    rw [normalize, denote_append _ _ coherent, hp env]
    change _ = Region.denote (ε := ε) (m := m) (Flat.link p.source q.source).typing env
    rw [Flat.denote_link _ _ coherent]
    congr 1
    funext out
    exact hq (PUnit.unit, merge out)
  | branch gate left right tail hl hr ht =>
    simp only [normalize, Normal.toSyntax, Syntax.source, Flat.denote_link _ _ coherent, ht]
    congr 1
    simp only [Flat.denote_fork _ _ _ coherent, hl, hr]

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
    {w : Reverse.Fibre (compile s)} (accepted : Reverse.recover (compile s) = some w)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.2.typing env).run initial =
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) s.source.typing env).run initial := by
  apply map_injective (ExplicitRuntime.exitTuple_injective (A := L))
  exact (Reverse.recover_observe accepted coherent env initial).symm.trans (compile_observe s coherent env initial)

end PartialState

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Normalization.Proofs
