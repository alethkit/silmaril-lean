module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Signature.Defs

public section

set_option backward.isDefEq.respectTransparency false

universe u v w x y z

namespace Silmaril.Isotope.LambdaSSA.Acyclic

open Morphism (SignatureMap)
open Morphism.CaseSSA (erase_mapInstr)

variable {Φ : Type u} {Ψ : Type v} {τ : Type w} {υ : Type x} {ε : Type y} {δ : Type z}
  [TypeFormers τ] [TypeFormers υ] [HasTy Φ τ] [HasTy Ψ υ] [HasEff Φ ε] [HasEff Ψ δ]
  (g : SignatureMap Φ Ψ τ υ ε δ) [g.PreservesProducts] [g.PreservesSums]
  {n : Nat} {β : BoundCtx τ n} {A : τ}

theorem toSSA_mapSignature_proof (c : Code Φ β A) (exit : Nat) :
    (c.mapSignature g).toSSA exit = (c.toSSA exit).mapInstr g.instr := by
  induction c generalizing exit <;>
    simp_all [Code.mapSignature, Code.toSSA, LambdaSSA.Region.mapInstr, Operand.castResult,
      Operand.mapSignature, erase_mapInstr]

theorem toLetCase_mapSignature_proof (c : Code Φ β A) :
    (c.mapSignature g).toLetCase = c.toLetCase.mapSignature g := by
  induction c with
  | br => rfl
  | @let₁ _ β B D a b ih =>
      let make (b' : Operand Ψ ((β.mapTypes g.ty).snoc (g.ty B)) (g.ty D)) :
          Operand Ψ (β.mapTypes g.ty) (g.ty D) :=
        ⟨.let₁ (a.1.mapInstr g.instr) b'.1, .let₁ (a.2.mapSignature g) b'.2⟩
      exact congrArg make ih
  | @let₂ _ β B C D a b ih =>
      let a' := (a.mapSignature g).castResult
        (SignatureMap.PreservesProducts.product (g := g) B C)
      let make (b' : Operand Ψ (((β.mapTypes g.ty).snoc (g.ty B)).snoc (g.ty C)) (g.ty D)) :
          Operand Ψ (β.mapTypes g.ty) (g.ty D) :=
        ⟨.let₂ a'.1 b'.1, .let₂ a'.2 b'.2⟩
      exact congrArg make ih
  | @case _ β B C D e l r ihl ihr =>
      let e' := (e.mapSignature g).castResult
        (SignatureMap.PreservesSums.coprod (g := g) B C)
      let make (l' : Operand Ψ ((β.mapTypes g.ty).snoc (g.ty B)) (g.ty D))
          (r' : Operand Ψ ((β.mapTypes g.ty).snoc (g.ty C)) (g.ty D)) :
          Operand Ψ (β.mapTypes g.ty) (g.ty D) :=
        ⟨.case e'.1 l'.1 r'.1, .case e'.2 l'.2 r'.2⟩
      exact congrArg₂ make ihl ihr
  | @join _ β B D a b iha ihb =>
      let make (a' : Operand Ψ (β.mapTypes g.ty) (g.ty B))
          (b' : Operand Ψ ((β.mapTypes g.ty).snoc (g.ty B)) (g.ty D)) :
          Operand Ψ (β.mapTypes g.ty) (g.ty D) :=
        ⟨.let₁ a'.1 b'.1, .let₁ a'.2 b'.2⟩
      exact congrArg₂ make iha ihb

private theorem ofLetCase_cast_br {n : Nat} {β : BoundCtx υ n} {A B : υ}
    {t : LetCase.LocallyNameless.Tm Empty Ψ n} (h : A = B)
    (d : LetCase.LocallyNameless.Derivation Ψ (.nil : Ctx Empty υ) β t A)
    (isBranch : Code.ofLetCase d = .br ⟨t, d⟩) :
    Code.ofLetCase (h ▸ d) = .br ⟨t, h ▸ d⟩ := by
  cases h
  exact isBranch

theorem ofLetCase_mapSignature_proof {t : LetCase.LocallyNameless.Tm Empty Φ n}
    (d : LetCase.LocallyNameless.Derivation Φ (.nil : Ctx Empty τ) β t A) :
    Code.ofLetCase (d.mapSignature g) = (Code.ofLetCase d).mapSignature g := by
  induction d with
  | @fv _ _ x => exact x.elim
  | let₁ _ _ iha ihb =>
      simp only [LetCase.LocallyNameless.Derivation.mapSignature, Code.ofLetCase,
        Code.mapSignature, iha, ihb]
  | let₂ _ _ _ ihb =>
      simp only [LetCase.LocallyNameless.Derivation.mapSignature, Code.ofLetCase,
        Code.mapSignature, ihb]
      rfl
  | case _ _ _ _ ihl ihr =>
      simp only [LetCase.LocallyNameless.Derivation.mapSignature, Code.ofLetCase,
        Code.mapSignature, ihl, ihr]
      rfl
  | abort => rfl
  | bv | op | unit | pair | inl | inr =>
      simp only [LetCase.LocallyNameless.Derivation.mapSignature, Code.ofLetCase, Code.mapSignature,
        Operand.mapSignature]
      apply ofLetCase_cast_br
      rfl

theorem ofLetCase_toSSA_congr_proof {t : LetCase.LocallyNameless.Tm Empty Φ n}
    (d : LetCase.LocallyNameless.Derivation Φ (.nil : Ctx Empty τ) β t A) :
    ∀ {β' : BoundCtx τ n} {A' : τ}
      (d' : LetCase.LocallyNameless.Derivation Φ (.nil : Ctx Empty τ) β' t A') (exit : Nat),
      (Code.ofLetCase d).toSSA exit = (Code.ofLetCase d').toSSA exit := by
  induction d with
  | @fv _ _ x => exact x.elim
  | let₁ _ _ iha ihb =>
      intro β' A' d' exit
      cases d' with
      | let₁ a b =>
          simp only [Code.ofLetCase, Code.toSSA, iha a, ihb b]
  | let₂ _ _ _ ihb =>
      intro β' A' d' exit
      cases d' with
      | let₂ a b => simp only [Code.ofLetCase, Code.toSSA, ihb b]
  | case _ _ _ _ ihl ihr =>
      intro β' A' d' exit
      cases d' with
      | case e l r => simp only [Code.ofLetCase, Code.toSSA, ihl l, ihr r]
  | bv | op | unit | pair | inl | inr | abort =>
      intro β' A' d' exit
      cases d'; rfl

end Silmaril.Isotope.LambdaSSA.Acyclic
