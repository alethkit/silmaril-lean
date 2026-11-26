module

public import Silmaril.SSA.RVSDG.LambdaSSA.Gamma.Thms

/-! # Single-exit λSSA regions and RVSDG

The region fragment allows value lets, payload cases and a branch to exit
zero. A branch argument is actual λSSA expression syntax. The existing
straight-line and terminal γ admissions apply to the recovered expression.
-/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA

open Silmaril.Isotope.LambdaSSA (Region Tm)

universe u v
variable {Φ : Type v}

/-- Move a CFG-free single-exit region into the corresponding expression.
Value and payload binders keep their de Bruijn indices. -/
def exitExpression : Region Φ → Option (Tm Φ)
  | .br 0 body => some body
  | .let₁ value body => (exitExpression body).map (.let₁ value)
  | .case discr left right =>
    match exitExpression left, exitExpression right with
    | some l, some r => some (.case discr l r)
    | _, _ => none
  | .br (_ + 1) _ | .let₂ _ _ | .cfg _ _ _ => none

/-- Syntactic correspondence for the three admitted region constructors. -/
inductive ExitExpression : Region Φ → Tm Φ → Prop
  | exit (body : Tm Φ) : ExitExpression (.br 0 body) body
  | let₁ {body : Region Φ} {expr : Tm Φ} (value : Tm Φ) :
      ExitExpression body expr → ExitExpression (.let₁ value body) (.let₁ value expr)
  | case {left right : Region Φ} {l r : Tm Φ} (discr : Tm Φ) :
      ExitExpression left l → ExitExpression right r →
      ExitExpression (.case discr left right) (.case discr l r)

/-- Choose a region with explicit region-level value lets and cases. -/
def exitRegion : Tm Φ → Region Φ
  | .let₁ value body => .let₁ value (exitRegion body)
  | .case discr l r => .case discr (exitRegion l) (exitRegion r)
  | body => .br 0 body

variable {τ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {Γ : List τ} {A : τ} {sigs : List (Ports (Ty τ))} {extra : Nat}

/-- A numbered graph and a region are related through their typed straight-line expression. -/
structure RegionRelated (r : Region Φ) (g : Graph (Opcode Φ) (inputs Γ) [] sigs [.value A]) where
  expression : Tm Φ
  represents : ExitExpression r expression
  graph : GraphRelated expression g

/-- A scoped terminal γ graph and a region are related through their typed case expression. -/
structure GammaRegionRelated (r : Region Φ) (g : GammaGraph Φ extra Γ A) where
  expression : Tm Φ
  represents : ExitExpression r expression
  graph : GammaGraphRelated expression g

/-- Form evidence for the recovered expression. -/
structure RegionForm (r : Region Φ) (Γ : List τ) (A : τ) where
  expression : Tm Φ
  represents : ExitExpression r expression
  form : SSAForm Γ expression A

/-- Form evidence for a scoped terminal switch. -/
structure GammaRegionForm (r : Region Φ) (extra : Nat) (Γ : List τ) (A : τ) where
  expression : Tm Φ
  represents : ExitExpression r expression
  form : GammaSSAForm extra expression Γ A

def lowerRegion {r : Region Φ} (h : RegionForm r Γ A) :
    Σ sigs, Σ g : Graph (Opcode Φ) (inputs Γ) [] sigs [.value A], RegionRelated r g :=
  let ⟨sigs, graph, rel⟩ := lowerGraph h.form
  ⟨sigs, graph, ⟨h.expression, h.represents, rel⟩⟩

def lowerGammaRegion {r : Region Φ} (h : GammaRegionForm r extra Γ A) :
    Σ g : GammaGraph Φ extra Γ A, GammaRegionRelated r g :=
  let ⟨graph, rel⟩ := lowerGammaGraph h.form
  ⟨graph, ⟨h.expression, h.represents, rel⟩⟩

end Silmaril.SSA.RVSDG.LambdaSSA
