module

public import Silmaril.SSA.Thesis.SyntacticCategory.Packing.Iteration.Defs
public import Silmaril.SSA.Thesis.SyntacticCategory.Packing.Thms

public section

universe u

namespace Silmaril.Thesis.LambdaIter.Syn.SynCat

open CategoryTheory LocallyNameless LocallyNameless.Tm LocallyNameless.Syntax

variable {S : Sig.{u}}

private theorem packedArrow_let_onNewest {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty}
    {a : Tm Empty S.Instr n} {k : Tm Empty S.Instr 1}
    (ha : HasType S.Instr Ctx.nil β a A) (hk : HasType S.Instr Ctx.nil (.snoc .nil A) k B) :
    packedArrow (S := S) (.let₁ ha (onNewestTyping hk)) = packedArrow ha ≫ mk hk := by
  have renameNewest : bsubst (upSub (project β (.bv 0))) (onNewest k) = underBinder k := by
    rw [onNewest, bsubst_rename, underBinder]
    change bsubst (fun _ : Fin 1 => .bv (0 : Fin 2)) k = _
    rw [bsubst_bv_eq_rename]
    exact rename_congr (Fin.cases rfl (fun i => i.elim0)) _
  apply Quotient.sound
  change Eqv S.pureEff Ctx.nil _ (.let₁ (packedTerm β a)
    (bsubst (upSub (project β (.bv 0))) (onNewest k)))
      (.let₁ (packedTerm β a) (underBinder k)) _
  rw [renameNewest]
  exact .refl (.let₁ (packedTyping ha) hk.underBinder)

private theorem packedArrow_iter_onNewest {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty}
    {a : Tm Empty S.Instr n} {b : Tm Empty S.Instr 1}
    (ha : HasType S.Instr Ctx.nil β a A)
    (hb : HasType S.Instr Ctx.nil (.snoc .nil A) b (coprod B A)) :
    packedArrow (S := S) (.iter ha (onNewestTyping hb)) = packedArrow ha ≫ iterate (mk hb) := by
  let step := onNewestTyping (β := β) hb
  let seed := HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty))
    (β := β) (A := A)
  let loop := HasType.iter HasType.newest hb.underBinder
  have shift : onNewest (n := n) (.iter (.bv 0) (underBinder b)) =
      .iter (.bv 0) (underBinder (onNewest (n := n) b)) := by
    simp only [onNewest, rename_iter, rename_bv, underBinder, rename_comp]
    congr 1
    exact rename_congr (Fin.cases rfl (fun i => i.elim0)) _
  have seq := Eqv.ax (.iteration (.iterBind (pureEff := S.pureEff) _ _))
    (.iter ha step) (.let₁ ha (.iter seed step.underBinder))
  rw [← shift] at seq
  exact ((packedArrow_eq_iff _ _).mpr seq).trans (packedArrow_let_onNewest ha loop)

private theorem packedArrow_packTerm {n : Nat} (β : BoundCtx S.Ty n) :
    packedArrow (S := S) (packTermTyping β) = 𝟙 (of (packType β)) := by
  apply Quotient.sound
  exact packed_unpacked β HasType.newest

theorem packedArrow_iter_state_proof {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty}
    {a : Tm Empty S.Instr n} {b : Tm Empty S.Instr (n + 1)}
    (ha : HasType S.Instr Ctx.nil β a A)
    (hb : HasType S.Instr Ctx.nil (β.snoc A) b (coprod B A)) :
    packedArrow (S := S) (.iter ha hb) =
      pairArrows (𝟙 (of (packType β))) (packedArrow ha) ≫
        iterate (packedArrow (carriedIterTyping hb)) := by
  let h := packTermTyping (S := S) (β.snoc A)
  let next := carriedIterTyping hb
  let nextPacked := packedTyping next
  let step := onNewestTyping (β := β) nextPacked
  have instantiated : ∀ k : Tm Empty S.Instr 1,
      instantiate (underBinder (onNewest (n := n) k)) (packTerm (β.snoc A)) =
        unpackedTerm (β.snoc A) k := by
    intro k
    rw [instantiate, underBinder, onNewest, bsubst_rename, bsubst_rename]
    rfl
  have square := (unpacked_packed next).symm
  rw [← instantiated] at square
  have simulation := Eqv.uniformity ha h (packTerm_pure _) hb step square
  calc
    _ = packedArrow (S := S) (.iter (.let₁ ha h) step) :=
      (packedArrow_eq_iff _ _).mpr simulation
    _ = packedArrow (.let₁ ha h) ≫ iterate (packedArrow next) :=
      packedArrow_iter_onNewest (.let₁ ha h) nextPacked
    _ = _ := by
      rw [packedArrow_let1, packedArrow_packTerm]
      exact congrArg (fun f => f ≫ iterate (packedArrow next)) (Category.comp_id _)

theorem packedArrow_carriedState_proof {n : Nat} (β : BoundCtx S.Ty n) (X A : S.Ty) :
    let R := of (S := S) (packType β)
    let P := productObj R (of X)
    packedArrow (S := S) ((packTermTyping (β.snoc A)).underBinder (X := X)) =
      pairArrows (first P (of A) ≫ first R (of X)) (second P (of A)) := by
  let old := ((packTermTyping (S := S) β).lift (B := X)).lift (B := A)
  let newest := HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty))
    (β := β.snoc X) (A := A)
  have tuple : underBinder (packTerm (S := S) (β.snoc A)) =
      .pair (lift (lift (packTerm β))) (.bv 0) := by
    simp only [packTerm, underBinder, rename_pair, rename_bv, lift, rename_comp]
    rfl
  have rep : packedArrow (S := S) ((packTermTyping (β.snoc A)).underBinder (X := X)) =
      packedArrow (HasType.pair old newest) := by
    apply Quotient.sound
    change Eqv S.pureEff Ctx.nil _ (packedTerm ((β.snoc X).snoc A)
      (underBinder (packTerm (β.snoc A)))) _ _
    rw [tuple]
    exact .refl (packedTyping (.pair old newest))
  have prev : packedArrow (S := S) old =
      first (productObj (of (packType β)) (of X)) (of A) ≫ first (of (packType β)) (of X) := by
    unfold old
    rw [packedArrow_lift, packedArrow_lift, packedArrow_packTerm]
    exact congrArg (fun f => first (productObj (of (packType β)) (of X)) (of A) ≫ f)
      (Category.comp_id _)
  rw [rep, packedArrow_pair, prev]
  rfl

end Silmaril.Thesis.LambdaIter.Syn.SynCat
