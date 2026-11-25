module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Tensor.Centrality.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Thms

/-! # Interchange with an empty input -/

public section

universe u v w

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.EmptyCentrality

open CategoryTheory Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Region.CfgEta (Eqv TypeCategory)
open Region.CfgEta.TypeCategory
open Silmaril.DeBruijn (lift)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

private def seqRegion (r s : Region Φ) : Region Φ :=
  r.lsubst (fun _ => s.renameVars (lift Nat.succ))

private theorem unpackedSeq {A B M N : τ} {p q : Region Φ}
    (hp : ValueBranches [B, A, Silmaril.product A B] p [M]) (hq : ValueBranches [M] q [N]) :
    ValueBranches [B, A, Silmaril.product A B]
      (p.lsubst (liftLSubstVars (liftLSubstVars (liftLSubstVars (fun _ => q))))) [N] :=
  hp.lsubst ((((singletonValueFamily hq).liftVars (Silmaril.product A B)).liftVars A).liftVars B)

private theorem unpackedSeq_eq_of_empty {A B M M' N : τ} {p p' q q' : Region Φ} {i : Nat}
    (hi : At [B, A, Silmaril.product A B] i (Silmaril.empty : τ))
    (hp : ValueBranches [B, A, Silmaril.product A B] p [M]) (hq : ValueBranches [M] q [N])
    (hp' : ValueBranches [B, A, Silmaril.product A B] p' [M']) (hq' : ValueBranches [M'] q' [N]) :
    Eqv [Silmaril.product A B] (seqRegion (.let₂ (.var 0) p) q)
      (seqRegion (.let₂ (.var 0) p') q') [N] :=
  .let₂ (.var rfl) (.native (.initial_var hi (unpackedSeq hp hq).hasType (unpackedSeq hp' hq').hasType))

private theorem seq_ofRegion {A B C : τ} {r s : Region Φ}
    (hr : ValueBranches [A] r [B]) (hs : ValueBranches [B] s [C]) :
    ofRegion (Γ := []) hr ≫ ofRegion (Γ := []) hs = ofRegion (seqValueBranches hr hs) := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem interchange_ofRegion {B X Y : τ} {p q : Region Φ}
    (hp : ValueBranches [Silmaril.empty] p [B]) (hq : ValueBranches [X] q [Y]) :
    (whiskerRight (ofRegion hp) (ofType X) ≫ whiskerLeft (ofType B) (ofRegion hq) =
       whiskerLeft (ofType Silmaril.empty) (ofRegion hq) ≫ whiskerRight (ofRegion hp) (ofType Y)) ∧
    (whiskerLeft (ofType X) (ofRegion hp) ≫ whiskerRight (ofRegion hq) (ofType B) =
       whiskerRight (ofRegion hq) (ofType Silmaril.empty) ≫ whiskerLeft (ofType Y) (ofRegion hp)) := by
  simp only [whiskerLeft_ofRegion, whiskerRight_ofRegion, seq_ofRegion]
  constructor
  · exact (ofRegion_eq_iff _ _).mpr (unpackedSeq_eq_of_empty (i := 1) rfl
      (whiskerRightBody_typed X hp) (whiskerLeftRegion_typed B hq)
      (whiskerLeftBody_typed Silmaril.empty hq) (whiskerRightRegion_typed Y hp))
  · exact (ofRegion_eq_iff _ _).mpr (unpackedSeq_eq_of_empty (i := 0) rfl
      (whiskerLeftBody_typed X hp) (whiskerRightRegion_typed B hq)
      (whiskerRightBody_typed Silmaril.empty hq) (whiskerLeftRegion_typed Y hp))

local notation "Comp" => TypeCategory Φ ([] : VCtx τ)

theorem whiskerCentral_of_empty_input {B : Comp} (f : ofType (Silmaril.empty : τ) ⟶ B) :
    WhiskerCentral f := by
  obtain ⟨p, hp, rfl⟩ := exists_region (A := (Silmaril.empty : τ)) (B := (show τ from B)) f
  intro X Y g
  obtain ⟨q, hq, rfl⟩ := exists_region (A := (show τ from X)) (B := (show τ from Y)) g
  exact interchange_ofRegion hp hq

variable {ε : Type w} [HasEff Φ ε]

theorem pureReturn_of_empty_input (pe : ε) {B : Comp} (f : ofType (Silmaril.empty : τ) ⟶ B) :
    PureReturn pe f := by
  have ht : Tm.HasType [Silmaril.empty] (.abort (.var 0) : Tm Φ) (show τ from B) := .abort (.var rfl)
  refine ⟨_, ht, .abort .var, returnRegion_typed ht, ?_⟩
  exact (emptyIsInitial (Φ := Φ) (Γ := [])).hom_ext f _

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.EmptyCentrality
