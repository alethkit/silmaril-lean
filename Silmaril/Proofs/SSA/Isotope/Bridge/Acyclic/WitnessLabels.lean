module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Pullback.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Labels.Thms

public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open Morphism (SignatureMap)
open LetIter.Semantics.Categorical (TypeModel)
open LambdaSSA.Semantics.Categorical
open scoped MonoidalCategory

variable {τ υ ε δ : Type} [TypeFormers τ] [TypeFormers υ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ}
  {V : Type 1} [Category.{0} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (g : SignatureMap P.Instr Q.Instr τ υ ε δ) [g.PreservesProducts] [g.PreservesSums]
  (M : TypeModel υ V)

omit [CartesianMonoidalCategory V] in
private theorem transported_ι_heq {n m : Nat} (hn : n = m) {F : Fin n → V} {G : Fin m → V}
    (hF : HEq F G) {i : Fin n} {j : Fin m} (hi : i.val = j.val) {A : V}
    (e : A = F i) (e' : A = G j) :
    HEq (eqToHom e ≫ Sigma.ι F i) (eqToHom e' ≫ Sigma.ι G j) := by
  subst m
  cases eq_of_heq hF
  have h := Fin.ext hi
  subst j
  rfl

theorem labelInject_heq {L : LambdaSSA.LCtx τ} {i : Nat} {A : τ} (h : LambdaSSA.At L i A) :
    HEq (labelInject (pullbackTypes g M) i h) (labelInject M i (mapContextLookup g.ty h)) := by
  unfold labelInject
  exact transported_ι_heq (List.length_map g.ty).symm (labelFamily_pullback g M L) rfl _ _

omit [CartesianMonoidalCategory V] in
private theorem heq_of_sigma_ι_comp {n m : Nat} (hn : n = m) {F : Fin n → V} {G : Fin m → V}
    (hF : HEq F G) {B D : V} (hD : B = D) {a : (∐ F) ⟶ B} {b : (∐ G) ⟶ D}
    (h : ∀ (i : Fin n) (j : Fin m), i.val = j.val → HEq (Sigma.ι F i ≫ a) (Sigma.ι G j ≫ b)) :
    HEq a b := by
  subst m
  cases eq_of_heq hF
  subst D
  apply heq_of_eq
  apply Sigma.hom_ext
  intro i
  exact eq_of_heq (h i i rfl)

private theorem labelInject_get_heq {σ : Type} [TypeFormers σ] (T : TypeModel σ V)
    {L : LambdaSSA.LCtx σ} (j : Fin L.length) {A : σ} (h : LambdaSSA.At L j.val A) :
    HEq (labelInject T j.val h) (Sigma.ι (fun k : Fin L.length => T.obj (L.get k)) j) := by
  have hA : L.get j = A := by
    have hk : L[j.val]? = some (L.get j) := by simp
    rw [h] at hk
    exact Option.some.inj hk.symm
  subst A
  unfold labelInject
  change HEq (eqToHom (rfl : T.obj (L.get j) = T.obj (L.get j)) ≫ _) _
  exact heq_of_eq (Category.id_comp _)

omit [CartesianMonoidalCategory V] [HasFiniteCoproducts V] in
private theorem comp_left_heq {A A' B D : V} (hA : A = A') {f : A ⟶ B} {f' : A' ⟶ B}
    (hf : HEq f f') (a : B ⟶ D) : HEq (f ≫ a) (f' ≫ a) := by
  subst A'
  cases eq_of_heq hf
  rfl

private theorem labelInject_index_eq {σ : Type} [TypeFormers σ] (T : TypeModel σ V)
    {L : LambdaSSA.LCtx σ} {i j : Nat} {A : σ} (e : i = j)
    (hi : LambdaSSA.At L i A) (hj : LambdaSSA.At L j A) :
    labelInject T i hi = labelInject T j hj := by subst j; rfl

private theorem labelInject_list_heq {σ : Type} [TypeFormers σ] (T : TypeModel σ V)
    {L L' : LambdaSSA.LCtx σ} {i : Nat} {A : σ} (e : L = L')
    (hi : LambdaSSA.At L i A) (hj : LambdaSSA.At L' i A) :
    HEq (labelInject T i hi) (labelInject T i hj) := by subst L'; rfl

private theorem labelHom_heq {L : LambdaSSA.LCtx τ} {L' : LambdaSSA.LCtx υ} (e : L.map g.ty = L')
    {B D : V} (hD : B = D) {a : labelObj (pullbackTypes g M) L ⟶ B} {b : labelObj M L' ⟶ D}
    (h : ∀ (i : Nat) (A : τ) (ha : LambdaSSA.At L i A) (hb : LambdaSSA.At L' i (g.ty A)),
      HEq (labelInject (pullbackTypes g M) i ha ≫ a) (labelInject M i hb ≫ b)) :
    HEq a b := by
  subst L'
  apply heq_of_sigma_ι_comp (List.length_map g.ty).symm (labelFamily_pullback g M L) hD
  intro i j hij
  let A := L.get i
  have hi : LambdaSSA.At L i.val A := by simp [LambdaSSA.At, A]
  have hj : LambdaSSA.At (L.map g.ty) j.val (g.ty A) := by rw [← hij]; exact mapContextLookup g.ty hi
  have eA : M.obj (g.ty A) = M.obj ((L.map g.ty).get j) := by
    simp only [A, List.get_eq_getElem, List.getElem_map, hij]
  have left := labelInject_get_heq (pullbackTypes g M) i hi
  have right := labelInject_get_heq M j hj
  have same := labelInject_index_eq M hij (mapContextLookup g.ty hi) hj
  exact (comp_left_heq rfl left a).symm.trans
    ((h i.val A hi (mapContextLookup g.ty hi)).trans
      ((heq_of_eq (congrArg (fun f => f ≫ b) same)).trans (comp_left_heq eA right b)))

omit [TypeFormers τ] [TypeFormers υ] in
theorem map_local_layout {n : Nat} (R : Fin n → τ) (L : LambdaSSA.LCtx τ) :
    (List.ofFn R ++ L).map g.ty = List.ofFn (g.ty ∘ R) ++ L.map g.ty := by
  rw [List.map_append, List.map_ofFn]

theorem labelObjToFinite_heq {n : Nat} (R : Fin n → τ) :
    HEq (labelObjToFinite (pullbackTypes g M) R) (labelObjToFinite M (g.ty ∘ R)) := by
  apply labelHom_heq g M List.map_ofFn rfl
  intro i A ha hb
  have hi : i < n := by
    have ha' := List.getElem?_eq_some_iff.mp ha
    simpa using ha'.1
  let j : Fin n := ⟨i, hi⟩
  have hA : R j = A := by
    have hn : LambdaSSA.At (List.ofFn R) i (R j) := by simp [LambdaSSA.At, j, hi]
    exact Option.some.inj (hn.symm.trans ha)
  subst A
  have e := labelObjToFinite_local (pullbackTypes g M) R j ha
  have e' := labelObjToFinite_local M (g.ty ∘ R) j hb
  exact (heq_of_eq e).trans (heq_of_eq e'.symm)

theorem labelAppendSplit_heq {n : Nat} (R : Fin n → τ) (L : LambdaSSA.LCtx τ) :
    HEq (labelAppendSplit (pullbackTypes g M) (List.ofFn R) L)
      (labelAppendSplit M (List.ofFn (g.ty ∘ R)) (L.map g.ty)) := by
  have hL := labelObj_pullback g M L
  have hR : labelObj (pullbackTypes g M) (List.ofFn R) = labelObj M (List.ofFn (g.ty ∘ R)) :=
    (labelObj_pullback g M (List.ofFn R)).trans (congrArg (labelObj M) List.map_ofFn)
  apply labelHom_heq g M (map_local_layout g R L) (congrArg₂ (fun X Y : V => X ⨿ Y) hL hR)
  intro i A ha hb
  by_cases hi : i < n
  · let j : Fin n := ⟨i, hi⟩
    have hA : R j = A := by
      have hn : LambdaSSA.At (List.ofFn R ++ L) i (R j) := by
        simp [LambdaSSA.At, List.getElem?_append_left, j, hi]
      exact Option.some.inj (hn.symm.trans ha)
    subst A
    have hs : LambdaSSA.At (List.ofFn R) i (R j) := by simp [LambdaSSA.At, j, hi]
    have ht : LambdaSSA.At (List.ofFn (g.ty ∘ R)) i (g.ty (R j)) := by
      simpa only [List.map_ofFn] using mapContextLookup g.ty hs
    have e := labelAppendSplit_local (pullbackTypes g M) R L j ha hs
    have e' := labelAppendSplit_local M (g.ty ∘ R) (L.map g.ty) j hb ht
    refine (heq_of_eq e).trans ?_
    apply HEq.trans _ (heq_of_eq e'.symm)
    have hj := (labelInject_heq g M hs).trans (labelInject_list_heq M List.map_ofFn _ ht)
    congr! (config := .unfoldSameFun)
  · obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
    have hs : LambdaSSA.At L j A := by
      simpa [LambdaSSA.At, List.getElem?_append_right] using ha
    have ht := mapContextLookup g.ty hs
    have e := labelAppendSplit_exit (pullbackTypes g M) R L hs ha
    have e' := labelAppendSplit_exit M (g.ty ∘ R) (L.map g.ty) ht hb
    refine (heq_of_eq e).trans ?_
    apply HEq.trans _ (heq_of_eq e'.symm)
    have hj := labelInject_heq g M hs
    congr! (config := .unfoldSameFun)

end Silmaril.Isotope.Institution.Acyclic
