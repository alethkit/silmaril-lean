module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Generation.Defs

/-! # The operations on generated singleton computations -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.Generation.Domain

open Silmaril Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

/-- The wide subcategory with precisely the generated arrows. -/
abbrev Category := WideSubcategory (generatedArrows Seed)

abbrev ofType (A : τ) : Category Seed := ⟨Singleton.ofType Seed A⟩

/-- Regard a generated ambient arrow as a morphism of the domain. -/
def ofGenerated {A B : τ} {f : Singleton.ofType Seed A ⟶ Singleton.ofType Seed B}
    (hf : Generated Seed f) : ofType Seed A ⟶ ofType Seed B := ⟨f, hf⟩

local notation "Obj" => ofType (Seed)

abbrev discard (A : τ) : Obj A ⟶ Obj (Silmaril.unit : τ) := ofGenerated Seed (.discard A)
abbrev fst (A B : τ) : Obj (product A B) ⟶ Obj A := ofGenerated Seed (.fst A B)
abbrev snd (A B : τ) : Obj (product A B) ⟶ Obj B := ofGenerated Seed (.snd A B)
abbrev diagonal (A : τ) : Obj A ⟶ Obj (product A A) := ofGenerated Seed (.copy A)
abbrev primitive (p : Φ) : Obj (instrSrc p) ⟶ Obj (instrTrg p) := ofGenerated Seed (.primitive p)
abbrev inl (A B : τ) : Obj A ⟶ Obj (coprod A B) := ofGenerated Seed (.inl A B)
abbrev inr (A B : τ) : Obj B ⟶ Obj (coprod A B) := ofGenerated Seed (.inr A B)

noncomputable def copair {A B D : τ} (f : Obj A ⟶ Obj D) (g : Obj B ⟶ Obj D) : Obj (coprod A B) ⟶ Obj D :=
  ofGenerated Seed (.copair f.property g.property)

def whiskerLeft (X : τ) {A B : τ} (f : Obj A ⟶ Obj B) : Obj (product X A) ⟶ Obj (product X B) :=
  ofGenerated Seed (.left X f.property)

def whiskerRight (X : τ) {A B : τ} (f : Obj A ⟶ Obj B) : Obj (product A X) ⟶ Obj (product B X) :=
  ofGenerated Seed (.right X f.property)

/-- Feedback of a generated exact-sum body is a domain morphism. -/
def iterateSum {A B : τ} (f : Obj A ⟶ Obj (coprod B A)) : Obj A ⟶ Obj B :=
  ofGenerated Seed (.iterate f.property)

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.Generation.Domain
