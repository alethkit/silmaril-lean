module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Defs

/-! # Change of primitive and type signatures in the exact acyclic fragment -/

@[expose] public section

universe u v w x y z k

namespace Silmaril.Isotope

open Morphism (SignatureMap)

variable {Φ : Type u} {Ψ : Type v} {τ : Type w} {υ : Type x} {ε : Type y} {δ : Type z}
  [TypeFormers τ] [TypeFormers υ] [HasTy Φ τ] [HasTy Ψ υ] [HasEff Φ ε] [HasEff Ψ δ]
  (g : SignatureMap Φ Ψ τ υ ε δ) [g.PreservesProducts] [g.PreservesSums]

namespace LetCase.LocallyNameless.Derivation

variable {ν : Type k} [DecidableEq ν] {Γ : Ctx ν τ}

/-- Relabel a derivation, transporting intermediate types through the same signature map. -/
def mapSignature : {n : Nat} → {β : BoundCtx τ n} → {t : Tm ν Φ n} → {A : τ} →
    Derivation Φ Γ β t A →
      Derivation Ψ (Γ.mapTypes g.ty) (β.mapTypes g.ty) (t.mapInstr g.instr) (g.ty A)
  | _, _, _, _, .fv h => .fv (by rw [Ctx.lookup_mapTypes, h]; rfl)
  | _, β, _, _, .bv (ι := i) => BoundCtx.get_mapTypes g.ty β i ▸ .bv
  | _, _, _, _, .op (f := f) a =>
      g.target f ▸ .op (f := g.instr f) ((g.source f).symm ▸ mapSignature a)
  | _, _, _, _, .let₁ a b => .let₁ (mapSignature a) (mapSignature b)
  | _, _, _, _, .unit => (SignatureMap.PreservesProducts.unit (g := g)).symm ▸ .unit
  | _, _, _, _, .pair (A := A) (B := B) a b =>
      (SignatureMap.PreservesProducts.product (g := g) A B).symm ▸
        .pair (mapSignature a) (mapSignature b)
  | _, _, _, _, .let₂ (A := A) (B := B) a b =>
      .let₂ (SignatureMap.PreservesProducts.product (g := g) A B ▸ mapSignature a)
        (mapSignature b)
  | _, _, _, _, .inl (A := A) (B := B) a =>
      (SignatureMap.PreservesSums.coprod (g := g) A B).symm ▸ .inl (mapSignature a)
  | _, _, _, _, .inr (A := A) (B := B) b =>
      (SignatureMap.PreservesSums.coprod (g := g) A B).symm ▸ .inr (mapSignature b)
  | _, _, _, _, .case (A := A) (B := B) e l r =>
      .case (SignatureMap.PreservesSums.coprod (g := g) A B ▸ mapSignature e)
        (mapSignature l) (mapSignature r)
  | _, _, _, _, .abort a =>
      .abort (SignatureMap.PreservesSums.empty (g := g) ▸ mapSignature a)

end LetCase.LocallyNameless.Derivation

namespace LambdaSSA.Acyclic

variable {n : Nat} {β : BoundCtx τ n} {A : τ}

/-- Transport only the result type of a typed operand. -/
def Operand.castResult {n : Nat} {β : BoundCtx υ n} {A B : υ}
    (h : A = B) (a : Operand Ψ β A) : Operand Ψ β B :=
  ⟨a.1, h ▸ a.2⟩

/-- Relabel a typed operand over the transported context and result. -/
def Operand.mapSignature (a : Operand Φ β A) : Operand Ψ (β.mapTypes g.ty) (g.ty A) :=
  ⟨a.1.mapInstr g.instr, a.2.mapSignature g⟩

/-- Change signature without altering the structure of joins or value binders. -/
def Code.mapSignature : {n : Nat} → {β : BoundCtx τ n} → {A : τ} →
    Code Φ β A → Code Ψ (β.mapTypes g.ty) (g.ty A)
  | _, _, _, .br a => .br (a.mapSignature g)
  | _, _, _, .let₁ a b => .let₁ (a.mapSignature g) (mapSignature b)
  | _, _, _, .let₂ (A := A) (B := B) a b =>
      .let₂ ((a.mapSignature g).castResult (SignatureMap.PreservesProducts.product (g := g) A B))
        (mapSignature b)
  | _, _, _, .case (A := A) (B := B) e l r =>
      .case ((e.mapSignature g).castResult (SignatureMap.PreservesSums.coprod (g := g) A B))
        (mapSignature l) (mapSignature r)
  | _, _, _, .join a b => .join (mapSignature a) (mapSignature b)

end LambdaSSA.Acyclic
end Silmaril.Isotope
