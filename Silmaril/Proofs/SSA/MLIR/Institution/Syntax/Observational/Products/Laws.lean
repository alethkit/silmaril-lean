module

public import Silmaril.SSA.MLIR.Institution.Syntax.Observational.Products.Defs

public section

namespace Silmaril.Proofs.MLIR.Institution.Syntax.Observational

open CategoryTheory Limits Silmaril.MLIR.Institution
open Silmaril.MLIR.Institution.Syntax.Observational

variable {withRegions : Bool} {S : Signature withRegions} {models : Model S → Prop}
variable {W X Y : Context models}

private theorem denote_transport {n : Nat} {Γ : Fin n → S.Ty} {a b : S.Ty}
    (h : a = b) (t : Term S Γ a) (M : Model S) (env : Assignment M.carrier Γ) :
    (h ▸ t : Term S Γ b).denote M env = h ▸ t.denote M env := by
  cases h
  rfl

theorem pairBlocks_rel {f f' : W.raw ⟶ X.raw} {g g' : W.raw ⟶ Y.raw}
    (hf : Rel models f f') (hg : Rel models g g') :
    Rel models (pairBlocks f g) (pairBlocks f' g') := by
  intro M hM env i
  refine Fin.addCases (motive := fun j =>
    (pairBlocks f g j).denote M env = (pairBlocks f' g' j).denote M env) ?_ ?_ i
  · intro j
    simp only [pairBlocks, Fin.addCases_left, denote_transport, hf M hM env j]
  · intro j
    simp only [pairBlocks, Fin.addCases_right, denote_transport, hg M hM env j]

theorem empty_unique (f : W ⟶ empty models) : f = ofBlock (fun i => Fin.elim0 i) := by
  refine Quotient.inductionOn f fun a => ?_
  exact Quotient.sound (fun _ _ _ i => Fin.elim0 i)

private theorem subst_projection {n m : Nat} {Γ : Fin n → S.Ty} {Δ : Fin m → S.Ty}
    (σ : Block S Γ Δ) (i : Fin m) {s : S.Ty} (h : Δ i = s) :
    (h ▸ Term.var i : Term S Δ s).subst σ = h ▸ σ i := by
  cases h
  rfl

private theorem transport_cancel {A : Type} {F : A → Type} {x y : A} (h : x = y) (t : F y) :
    (h ▸ (h.symm ▸ t : F x) : F y) = t := by
  cases h
  rfl

private theorem transport_injective {A : Type} {F : A → Type} {x y : A} (h : x = y) :
    Function.Injective (fun t : F x => (h ▸ t : F y)) := by
  cases h
  exact fun _ _ h => h

theorem pair_fst (f : W.raw ⟶ X.raw) (g : W.raw ⟶ Y.raw) :
    ofBlock (pairBlocks f g) ≫ fst X Y = ofBlock f := by
  apply congrArg ofBlock
  funext i
  change ((append_left X Y i ▸ .var _) : Term S (append X Y).raw.ty _).subst _ = f i
  simp only [subst_projection, pairBlocks, Fin.addCases_left, transport_cancel]

theorem pair_snd (f : W.raw ⟶ X.raw) (g : W.raw ⟶ Y.raw) :
    ofBlock (pairBlocks f g) ≫ snd X Y = ofBlock g := by
  apply congrArg ofBlock
  funext i
  change ((append_right X Y i ▸ .var _) : Term S (append X Y).raw.ty _).subst _ = g i
  simp only [subst_projection, pairBlocks, Fin.addCases_right, transport_cancel]

theorem append_hom_ext {f g : W ⟶ append X Y}
    (hl : f ≫ fst X Y = g ≫ fst X Y) (hr : f ≫ snd X Y = g ≫ snd X Y) : f = g := by
  revert hl hr
  refine Quotient.inductionOn₂ f g fun a b hl hr => Quotient.sound ?_
  intro M hM env i
  refine Fin.addCases (motive := fun j => (a j).denote M env = (b j).denote M env) ?_ ?_ i
  · intro j
    have h := Quotient.exact (s := homSetoid W X) hl M hM env j
    let k := j.castAdd Y.raw.length
    have e := append_left X Y j
    change ((e ▸ Term.var k : Term S (append X Y).raw.ty (X.raw.ty j)).subst a).denote M env =
      ((e ▸ Term.var k : Term S (append X Y).raw.ty (X.raw.ty j)).subst b).denote M env at h
    simp only [subst_projection, denote_transport] at h
    exact transport_injective e h
  · intro j
    have h := Quotient.exact (s := homSetoid W Y) hr M hM env j
    let k := j.natAdd X.raw.length
    have e := append_right X Y j
    change ((e ▸ Term.var k : Term S (append X Y).raw.ty (Y.raw.ty j)).subst a).denote M env =
      ((e ▸ Term.var k : Term S (append X Y).raw.ty (Y.raw.ty j)).subst b).denote M env at h
    simp only [subst_projection, denote_transport] at h
    exact transport_injective e h

end Silmaril.Proofs.MLIR.Institution.Syntax.Observational
