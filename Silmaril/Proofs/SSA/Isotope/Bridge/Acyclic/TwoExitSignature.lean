module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.TwoExit.Signature.Defs

public section

set_option backward.isDefEq.respectTransparency false

universe u v w x y z

namespace Silmaril.Isotope.LambdaSSA.Acyclic.TwoExit

open Morphism (SignatureMap)
open Morphism.CaseSSA (erase_mapInstr)

variable {Φ : Type u} {Ψ : Type v} {τ : Type w} {υ : Type x} {ε : Type y} {δ : Type z}
  [TypeFormers τ] [TypeFormers υ] [HasTy Φ τ] [HasTy Ψ υ] [HasEff Φ ε] [HasEff Ψ δ]
  (g : SignatureMap Φ Ψ τ υ ε δ) [g.PreservesProducts] [g.PreservesSums]
  {A B : τ} {n : Nat} {β : BoundCtx τ n}

private theorem toSSA_cast {X Y : υ} {γ : BoundCtx υ n} (h : X = Y) (c : Code Ψ γ X) :
    (h ▸ c : Code Ψ γ Y).toSSA 0 = c.toSSA 0 := by
  cases h
  rfl

theorem toSSA_mapSignature_proof (c : TwoExit Φ A B β) :
    (c.mapSignature g).toSSA = c.toSSA.mapInstr g.instr := by
  induction c with
  | left a => simp [mapSignature, toSSA, Operand.mapSignature, Region.mapInstr, erase_mapInstr]
  | right b => simp [mapSignature, toSSA, Operand.mapSignature, Region.mapInstr, erase_mapInstr]
  | case e l r ihl ihr =>
    simp [mapSignature, toSSA, Operand.mapSignature, Operand.castResult, Region.mapInstr,
      erase_mapInstr, ihl, ihr]
  | dispatch c =>
    simp only [mapSignature, toSSA, toSSA_cast, Code.toSSA_mapSignature, Region.linkExits,
      Region.mapInstr, Region.mapInstr_renameLabels]
    rfl

private theorem cast_branch {X Y : υ} {γ : BoundCtx υ n} (h : X = Y) (a : Operand Ψ γ X) :
    (h ▸ Code.br a : Code Ψ γ Y) = .br (a.castResult h) := by
  cases h
  rfl

private theorem cast_case {X Y D E : υ} {γ : BoundCtx υ n} (h : D = E)
    (e : Operand Ψ γ (coprod X Y)) (l : Code Ψ (γ.snoc X) D) (r : Code Ψ (γ.snoc Y) D) :
    (h ▸ Code.case e l r : Code Ψ γ E) = .case e (h ▸ l) (h ▸ r) := by
  cases h
  rfl

omit [TypeFormers υ] in
private theorem cast_back {X Y : υ} {F : υ → Type*} (h : X = Y) (a : F Y) :
    (h ▸ (h.symm ▸ a : F X) : F Y) = a := by
  cases h
  rfl

theorem encode_mapSignature_proof (c : TwoExit Φ A B β) :
    (c.mapSignature g).encode =
      (SignatureMap.PreservesSums.coprod (g := g) A B ▸ c.encode.mapSignature g :
        Code Ψ (β.mapTypes g.ty) (coprod (g.ty A) (g.ty B))) := by
  induction c with
  | left a =>
    simp only [mapSignature, encode, Code.mapSignature, cast_branch, Operand.mapSignature,
      Operand.castResult, LetCase.LocallyNameless.Derivation.mapSignature,
      LetCase.LocallyNameless.Tm.mapInstr, cast_back]
  | right b =>
    simp only [mapSignature, encode, Code.mapSignature, cast_branch, Operand.mapSignature,
      Operand.castResult, LetCase.LocallyNameless.Derivation.mapSignature,
      LetCase.LocallyNameless.Tm.mapInstr, cast_back]
  | case e l r ihl ihr =>
    simp only [mapSignature, encode, Code.mapSignature, cast_case, ihl, ihr]
  | dispatch c => rfl

end Silmaril.Isotope.LambdaSSA.Acyclic.TwoExit
