module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Sentence.Defs

public section

set_option backward.isDefEq.respectTransparency false

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory
open LambdaSSA.Acyclic (Code Operand)
open Isotope.LetCase.LocallyNameless (Tm Derivation)
open Morphism.CaseSSA (erase_mapInstr)

variable {τ ε : Type} [TypeFormers τ] {P Q S : InstrSig τ ε} {n : Nat}
  {β : BoundCtx τ n} {A B D : τ}

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)

private theorem leftSide_heq {e e' : CaseEquation P} (h : e = e') :
    HEq e.2.1 e'.2.1 := by
  cases h
  rfl

private theorem mapOperand_id (a : Operand P.Instr β A) : mapOperand (𝟙 P) a = a := by
  let e : CaseEquation P := ⟨⟨n, β, A⟩, a, a⟩
  let F := LetCase.inst (ε := ε) Γ₀
  have h := congrArg (fun (k : F.obj P ⟶ F.obj P) => k.sen e) (F.map_id P)
  exact eq_of_heq (leftSide_heq h)

private theorem mapOperand_comp (g : P ⟶ Q) (h : Q ⟶ S) (a : Operand P.Instr β A) :
    mapOperand (g ≫ h) a = mapOperand h (mapOperand g a) := by
  let e : CaseEquation P := ⟨⟨n, β, A⟩, a, a⟩
  let F := LetCase.inst (ε := ε) Γ₀
  have agree := congrArg (fun (k : F.obj P ⟶ F.obj S) => k.sen e) (F.map_comp g h)
  exact eq_of_heq (leftSide_heq agree)

theorem mapCode_id_proof (c : Code P.Instr β A) : mapCode (𝟙 P) c = c := by
  induction c <;> simp_all only [mapCode, mapOperand_id]

theorem mapCode_comp_proof (g : P ⟶ Q) (h : Q ⟶ S) (c : Code P.Instr β A) :
    mapCode (g ≫ h) c = mapCode h (mapCode g c) := by
  induction c <;> simp_all only [mapCode, mapOperand_comp]

private theorem mapOperand_fst (g : P ⟶ Q) (a : Operand P.Instr β A) :
    (mapOperand g a).1 = a.1.mapInstr g.instr :=
  LetCase.translate_fst Γ₀ g (i := ⟨n, β, A⟩) a

theorem mapCode_toSSA_proof (g : P ⟶ Q) (c : Code P.Instr β A) (exit : Nat) :
    (mapCode g c).toSSA exit = (c.toSSA exit).mapInstr (InstrSig.Hom.instr g) := by
  induction c generalizing exit <;>
    simp_all only [mapCode, Code.toSSA, LambdaSSA.Region.mapInstr, mapOperand_fst, erase_mapInstr]

private theorem mapOperand_let₁ (g : P ⟶ Q) (a : Operand P.Instr β A)
    (b : Operand P.Instr (β.snoc A) B) :
    mapOperand g ⟨.let₁ a.1 b.1, .let₁ a.2 b.2⟩ =
      ⟨.let₁ (mapOperand g a).1 (mapOperand g b).1,
        .let₁ (mapOperand g a).2 (mapOperand g b).2⟩ := rfl

private theorem mapOperand_let₂ (g : P ⟶ Q) (a : Operand P.Instr β (product A B))
    (b : Operand P.Instr ((β.snoc A).snoc B) D) :
    mapOperand g ⟨.let₂ a.1 b.1, .let₂ a.2 b.2⟩ =
      ⟨.let₂ (mapOperand g a).1 (mapOperand g b).1,
        .let₂ (mapOperand g a).2 (mapOperand g b).2⟩ := rfl

private theorem mapOperand_case (g : P ⟶ Q) (e : Operand P.Instr β (coprod A B))
    (l : Operand P.Instr (β.snoc A) D) (r : Operand P.Instr (β.snoc B) D) :
    mapOperand g ⟨.case e.1 l.1 r.1, .case e.2 l.2 r.2⟩ =
      ⟨.case (mapOperand g e).1 (mapOperand g l).1 (mapOperand g r).1,
        .case (mapOperand g e).2 (mapOperand g l).2 (mapOperand g r).2⟩ := rfl

private theorem mapCode_toLetCase (g : P ⟶ Q) (c : Code P.Instr β A) :
    (mapCode g c).toLetCase = mapOperand g c.toLetCase := by
  induction c with
  | br => rfl
  | @let₁ _ β A B a b ih =>
      let pack (b' : Operand Q.Instr (β.snoc A) B) : Operand Q.Instr β B :=
        ⟨.let₁ (mapOperand g a).1 b'.1, .let₁ (mapOperand g a).2 b'.2⟩
      exact (congrArg pack ih).trans (mapOperand_let₁ g a b.toLetCase).symm
  | @let₂ _ β A B D a b ih =>
      let pack (b' : Operand Q.Instr ((β.snoc A).snoc B) D) : Operand Q.Instr β D :=
        ⟨.let₂ (mapOperand g a).1 b'.1, .let₂ (mapOperand g a).2 b'.2⟩
      exact (congrArg pack ih).trans (mapOperand_let₂ g a b.toLetCase).symm
  | @case _ β A B D e l r ihl ihr =>
      let pack (l' : Operand Q.Instr (β.snoc A) D)
          (r' : Operand Q.Instr (β.snoc B) D) : Operand Q.Instr β D :=
        ⟨.case (mapOperand g e).1 l'.1 r'.1, .case (mapOperand g e).2 l'.2 r'.2⟩
      exact (congrArg₂ pack ihl ihr).trans (mapOperand_case g e l.toLetCase r.toLetCase).symm
  | @join _ β A B a b iha ihb =>
      let pack (a' : Operand Q.Instr β A)
          (b' : Operand Q.Instr (β.snoc A) B) : Operand Q.Instr β B :=
        ⟨.let₁ a'.1 b'.1, .let₁ a'.2 b'.2⟩
      exact (congrArg₂ pack iha ihb).trans (mapOperand_let₁ g a.toLetCase b.toLetCase).symm

theorem compile_natural_proof (g : P ⟶ Q) (e : SSAEquation P) :
    compile (mapEquation g e) = ((LetCase.inst Γ₀).map g).sen (compile e) := by
  obtain ⟨⟨n, β, A⟩, a, b⟩ := e
  exact congrArg₂ (fun x y => (⟨⟨n, β, A⟩, x, y⟩ : CaseEquation Q))
    (mapCode_toLetCase g a) (mapCode_toLetCase g b)

private def isBranchRoot {Φ : Type} (t : Tm Empty Φ n) : Prop :=
  match t with
  | .let₁ .. | .let₂ .. | .case .. => False
  | _ => True

private theorem ofLetCase_branchRoot {t : Tm Empty P.Instr n}
    (d : Derivation P.Instr Γ₀ β t A) (h : isBranchRoot t) :
    Code.ofLetCase d = .br ⟨t, d⟩ := by
  cases d with
  | @fv _ _ x => exact x.elim
  | _ => first | rfl | exact h.elim

private theorem ofLetCase_mapOperand (g : P ⟶ Q) {t : Tm Empty P.Instr n}
    (d : Derivation P.Instr Γ₀ β t A) :
    Code.ofLetCase (mapOperand g ⟨t, d⟩).2 = mapCode g (Code.ofLetCase d) := by
  induction d with
  | @fv _ _ x => exact x.elim
  | let₁ da db iha ihb =>
      exact congrArg₂ Code.join iha ihb
  | let₂ da db _ ihb =>
      exact congrArg (Code.let₂ (mapOperand g ⟨_, da⟩)) ihb
  | case de dl dr _ ihl ihr =>
      exact congrArg₂ (Code.case (mapOperand g ⟨_, de⟩)) ihl ihr
  | bv | op | unit | pair | inl | inr | abort =>
      apply ofLetCase_branchRoot
      rw [mapOperand_fst]
      trivial

theorem reify_natural_proof (g : P ⟶ Q) (e : CaseEquation P) :
    reify (((LetCase.inst Γ₀).map g).sen e) = mapEquation g (reify e) := by
  obtain ⟨⟨n, β, A⟩, ⟨a, da⟩, ⟨b, db⟩⟩ := e
  exact congrArg₂ (fun x y => (⟨⟨n, β, A⟩, x, y⟩ : SSAEquation Q))
    (ofLetCase_mapOperand g da) (ofLetCase_mapOperand g db)

end Silmaril.Isotope.Institution.Acyclic
