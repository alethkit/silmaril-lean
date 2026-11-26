module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.OrdinarySquare.Defs

/-! # Opt-in binary-fold simulation for guarded CFGs -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold

open CategoryTheory CategoryTheory.Limits
open Silmaril Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Paper.BoundSimulation

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- Inspect the tag, and forward its payload on both arms. -/
abbrev foldTerm : Tm Φ := .case (.var 0) (.var 0) (.var 0)

theorem fold_typed {Γ : VCtx τ} (X : τ) : Tm.HasType (Silmaril.coprod X X :: Γ) (foldTerm (Φ := Φ)) X :=
  .case (.var rfl) (.var rfl) (.var rfl)

/-- A standalone simulation seed for one state-map shape and an actual case-return local square. -/
inductive FoldStep : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop where
  | simulate {Γ : VCtx τ} {L : LCtx τ} {X : τ} {entry p q : Region Φ}
      (he : ValueBranches Γ entry (Silmaril.coprod X X :: L))
      (hp : ValueBranches (Silmaril.coprod X X :: Γ) p (Silmaril.coprod X X :: L))
      (hq : ValueBranches (X :: Γ) q (X :: L))
      (square : Paper.WithCaseReturns.Eqv pe (Silmaril.coprod X X :: Γ)
        (p.lsubst (liftLSubstVars (boundLocalMap foldTerm)))
        ((Region.br 0 foldTerm).bindBranchArguments.lsubst (liftLSubstVars (fun _ => q))) (X :: L)) :
      FoldStep Γ (.cfg entry 1 (fun _ => p))
        (.cfg (entry.lsubst (boundLocalMap foldTerm)) 1 (fun _ => q)) L

/-- Standalone opt-in extension of the existing case-return seed. -/
abbrev JoinedStep (Γ : VCtx τ) (r s : Region Φ) (L : LCtx τ) : Prop :=
  Paper.WithCaseReturns.JoinedStep pe Γ r s L ∨ FoldStep pe Γ r s L

/-- The contextual closure of the case-return equations and the binary-fold seed. -/
abbrev Eqv := Paper.Extension.Eqv (JoinedStep (τ := τ) (Φ := Φ) pe)

/-- The separately named singleton computation quotient. -/
abbrev TypeCategory := Paper.Extension.Singleton.TypeCategory (JoinedStep (τ := τ) (Φ := Φ) pe)

local notation "Obj" => Paper.TypeCategory.ofType (Φ := Φ)

/-- Alternate the two state tags on every repeat, leaving outward results unchanged. -/
noncomputable def alternatingStep {A B : τ} (q : Obj A ⟶ Obj B ⨿ Obj A) :
    Obj (Silmaril.coprod A A) ⟶ Obj B ⨿ Obj (Silmaril.coprod A A) :=
  (Paper.TypeCategory.sumIso A A).hom ≫
    coprod.desc (q ≫ coprod.map (𝟙 _) (Paper.TypeCategory.sumCofan A A).inr)
                (q ≫ coprod.map (𝟙 _) (Paper.TypeCategory.sumCofan A A).inl)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold
