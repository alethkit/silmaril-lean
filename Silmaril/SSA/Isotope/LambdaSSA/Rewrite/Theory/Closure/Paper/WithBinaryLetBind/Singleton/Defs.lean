module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBinaryLetBind.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.BinaryLet.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.PackedBody.Thms

/-! # The binary-let extension on singleton arrows -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBinaryLetBind.Singleton

open CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- The Paper singleton category quotiented by the binary-let extension. -/
abbrev TypeCategory (Φ : Type v) [HasTy Φ τ] :=
  Extension.Singleton.TypeCategory (BinaryLetBind.Step (τ := τ) (Φ := Φ))

abbrev projection : Paper.TypeCategory (τ := τ) Φ ⥤ TypeCategory (τ := τ) Φ :=
  Extension.Singleton.projection BinaryLetBind.Step

abbrev ofType (A : τ) : TypeCategory (τ := τ) Φ :=
  (projection (Φ := Φ)).obj (Paper.TypeCategory.ofType (Φ := Φ) A)

abbrev ofRegion {A B : τ} {r : Region Φ} (hr : ValueBranches [A] r [B]) :
    ofType (Φ := Φ) A ⟶ ofType (Φ := Φ) B :=
  (projection (Φ := Φ)).map (Paper.TypeCategory.ofRegion hr)

abbrev whiskerLeftFunctor (X : TypeCategory (τ := τ) Φ) :
    TypeCategory (τ := τ) Φ ⥤ TypeCategory (τ := τ) Φ :=
  Extension.Singleton.whiskerLeftFunctor BinaryLetBind.Step X

open Paper.PackedBody (applyPacked_typed)
open Paper.SingletonReification.BinaryLet (applyPackedPair_typed)

/-- Loop-free singleton representatives with each retained body on a packed
input. A binary let requires the exact scrutinee typing. -/
inductive LoopFree : {X D : τ} → {r : Region Φ} → ValueBranches [X] r [D] → Prop where
  | branch {X D : τ} {a : Tm Φ} (ha : Tm.BranchValue [X] a D) :
      LoopFree (.br (ℓ := 0) rfl ha)
  | let₁ {X A D : τ} {a : Tm Φ} {p : Region Φ}
      (ha : Tm.HasType [X] a A) {hp : ValueBranches [Silmaril.product X A] p [D]}
      (body : LoopFree hp) : LoopFree (.let₁ ha (applyPacked_typed hp))
  | let₂ {X A B D : τ} {a : Tm Φ} {p : Region Φ}
      (ha : Tm.HasType [X] a (Silmaril.product A B))
      {hp : ValueBranches [Silmaril.product X (Silmaril.product A B)] p [D]}
      (body : LoopFree hp) : LoopFree (.let₂ ha (applyPackedPair_typed hp))
  | case {X A B D : τ} {a : Tm Φ} {p q : Region Φ}
      (ha : Tm.HasType [X] a (Silmaril.coprod A B))
      {hp : ValueBranches [Silmaril.product X A] p [D]}
      {hq : ValueBranches [Silmaril.product X B] q [D]}
      (left : LoopFree hp) (right : LoopFree hq) :
      LoopFree (.case ha (applyPacked_typed hp) (applyPacked_typed hq))
  | cfgZero {X D : τ} {p : Region Φ} {hp : ValueBranches [X] p [D]}
      (entry : LoopFree hp) (blocks : Fin 0 → Region Φ) :
      LoopFree (.cfg Fin.elim0 hp (fun i => i.elim0) :
        ValueBranches [X] (.cfg p 0 blocks) [D])

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBinaryLetBind.Singleton
