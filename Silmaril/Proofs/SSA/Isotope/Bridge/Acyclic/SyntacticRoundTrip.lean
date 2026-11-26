module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Syntactic.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Syntactic.Join.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.BranchNormalization.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms

/-! # The guarded syntactic round trip for structured acyclic code -/

public section

universe u v w

namespace Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.SyntacticRoundTrip

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open LambdaSSA.Acyclic Region
open LetCase.LocallyNameless (Derivation)
open Morphism.CaseSSA (erase erase_hasType)
open Silmaril.DeBruijn (lift liftN)
open CfgEta (singleCfg)
open CfgEta.TypeCategory (returnRegion returnRegion_typed caseValueBranches)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

local notation "Seed" => RoundTripSeed (τ := τ) (Φ := Φ) pe
local notation "Eqv" => Paper.Extension.Eqv (Seed)
local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)

theorem guarded_typed {n : Nat} {β : BoundCtx τ n} {A : τ} (c : Code Φ β A)
    {L : LCtx τ} {exit : Nat} (h : At L exit A) : ValueBranches β.toList (c.guardedSSA exit) L :=
  (c.toSSA_hasType h).bindBranchArguments

private theorem guarded_rename {n : Nat} {β : BoundCtx τ n} {A : τ} (c : Code Φ β A)
    (exit : Nat) (ρ : Nat → Nat) : (c.guardedSSA exit).renameLabels ρ = c.guardedSSA (ρ exit) := by
  induction c generalizing exit ρ with
  | br => rfl
  | let₁ _ _ ih =>
    simp only [Code.guardedSSA, Code.toSSA, bindBranchArguments, renameLabels] at ih ⊢
    rw [ih]
  | let₂ _ _ ih =>
    simp only [Code.guardedSSA, Code.toSSA, bindBranchArguments, renameLabels] at ih ⊢
    rw [ih]
  | case _ _ _ ihl ihr =>
    simp only [Code.guardedSSA, Code.toSSA, bindBranchArguments, renameLabels] at ihl ihr ⊢
    rw [ihl, ihr]
  | join _ _ ihe ihb =>
    simp only [Code.guardedSSA, Code.toSSA, bindBranchArguments, renameLabels] at ihe ihb ⊢
    simp only [ihe, ihb, liftN, lift]

include pe in
private theorem joinCongr {Γ : VCtx τ} {L : LCtx τ} {A : τ} {e e' b b' : Region Φ}
    (he : Eqv Γ e e' (A :: L)) (hb : Eqv (A :: Γ) b b' (A :: L)) :
    Eqv Γ (singleCfg e b) (singleCfg e' b') L := by
  let R : Fin 1 → τ := fun _ => A
  have hR : List.ofFn R ++ L = A :: L := by simp [R, List.ofFn_succ]
  exact .cfg R (hR.symm ▸ he) (fun _ => hR.symm ▸ hb)

include pe in
private theorem letToJoin {Γ : VCtx τ} {L : LCtx τ} {A : τ} {a : Tm Φ} {b p : Region Φ}
    (ha : Tm.HasType Γ a A) (hb : ValueBranches (A :: Γ) b L)
    (entry : Eqv Γ (Region.br 0 a).bindBranchArguments p (A :: L)) :
    Eqv Γ (.let₁ a b) (singleCfg p (b.renameLabels Nat.succ)) L := by
  have h0 : ValueBranches Γ (Region.br 0 a).bindBranchArguments [A] :=
    (HasType.br (ℓ := 0) (rfl : At [A] 0 A) ha).bindBranchArguments
  have linked := Paper.linkedJoin h0 hb
  rw [lsubst_bindBranchArguments_br] at linked
  have shifted := hb.hasType.renameLabels (Ren.wk L A)
  exact (Paper.Extension.Eqv.paper linked.symm).trans (joinCongr pe entry (.refl shifted))

private theorem constructor_reifies_as_branch {n : Nat} {β : BoundCtx τ n} {D A : τ}
    {t : LetCase.LocallyNameless.Tm Empty Φ n} {Γ : VCtx τ}
    (d : Derivation Φ Γ₀ β t D) (h : Tm.BranchValue Γ (erase t) A) (exit : Nat) :
    (Code.ofLetCase d).toSSA exit = .br exit (erase t) := by
  cases d with
  | @fv _ _ x => exact x.elim
  | let₁ | let₂ | case => cases h
  | _ => rfl

private theorem value_rename {Γ Δ : VCtx τ} {t : Tm Φ} {D : τ} {ρ : Nat → Nat}
    (h : Tm.BranchValue Γ t D) (r : Ren Γ Δ ρ) : Tm.BranchValue Δ (t.rename ρ) D := by
  have hb : ValueBranches Γ (Region.br 0 t) [D] := .br rfl h
  have hr : ValueBranches Δ (Region.br 0 (t.rename ρ)) [D] := hb.renameVars r
  cases hr with
  | br hi h => cases Option.some.inj hi; exact h

omit [HasTy Φ τ] in
private theorem value_pure {Γ : VCtx τ} {t : Tm Φ} {D : τ} (h : Tm.BranchValue Γ t D) : Tm.Pure pe t := by
  induction h with
  | var => exact .var
  | unit => exact .unit
  | pair _ _ ih1 ih2 => exact .pair ih1 ih2
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih

omit [TypeFormers τ] in
private theorem singletonRen {D : τ} {L : LCtx τ} {exit : Nat} (hi : At L exit D) :
    Ren [D] L (fun _ => exit) := by
  intro i T h
  have iz : i = 0 := by simpa using (List.getElem?_eq_some_iff.mp h).1
  subst i
  cases Option.some.inj h
  exact hi

include pe in
private theorem splitReturn {A B D : τ} {a b : Tm Φ} {L : LCtx τ} {exit : Nat}
    (ha : Tm.BranchValue [A] a D) (hb : Tm.BranchValue [B] b D) (hi : At L exit D) :
    Eqv [coprod A B]
      (Region.br exit (.case (.var 0) (a.rename (lift Nat.succ)) (b.rename (lift Nat.succ)))).bindBranchArguments
      (.case (.var 0) (Region.br exit (a.rename (lift Nat.succ))).bindBranchArguments
        (Region.br exit (b.rename (lift Nat.succ))).bindBranchArguments) L := by
  let S := coprod A B
  have left := (ha.hasType.rename ((Ren.wk [] S).lift A))
  have right := (hb.hasType.rename ((Ren.wk [] S).lift B))
  have whole : Tm.HasType [S]
      (.case (.var 0) (a.rename (lift Nat.succ)) (b.rename (lift Nat.succ))) D :=
    .case (.var rfl) left right
  have step : Eqv [S]
      (returnRegion (.case (.var 0) (a.rename (lift Nat.succ)) (b.rename (lift Nat.succ))))
      (.case (.var 0) ((returnRegion a).renameVars (lift Nat.succ))
        ((returnRegion b).renameVars (lift Nat.succ))) [D] :=
    .extra (returnRegion_typed whole).hasType
      (caseValueBranches (returnRegion_typed ha.hasType) (returnRegion_typed hb.hasType)).hasType
      (.inr (.split ha.hasType hb.hasType (value_pure pe ha) (value_pure pe hb)))
  have widened := step.renameLabels (singletonRen hi)
  have aeq : returnRegion a = (Region.br 0 a).bindBranchArguments := by cases ha <;> rfl
  have beq : returnRegion b = (Region.br 0 b).bindBranchArguments := by cases hb <;> rfl
  simpa only [aeq, beq, returnRegion, bindBranchArguments, renameLabels, renameVars, Tm.rename, lift]
    using widened

include pe in
private theorem reflBr {n : Nat} {β : BoundCtx τ n} {D : τ}
    {t : LetCase.LocallyNameless.Tm Empty Φ n} (d : Derivation Φ Γ₀ β t D)
    {L : LCtx τ} {exit : Nat} (hi : At L exit D) :
    Eqv β.toList (Region.br exit (erase t)).bindBranchArguments
      (Region.br exit (erase t)).bindBranchArguments L :=
  .refl (guarded_typed (Code.br ⟨_, d⟩) hi).hasType

include pe in
theorem operand {n : Nat} {β : BoundCtx τ n} {t : LetCase.LocallyNameless.Tm Empty Φ n} {D : τ}
    (d : Derivation Φ Γ₀ β t D) (admitted : Operand.admittedDerivation d)
    {L : LCtx τ} {exit : Nat} (hi : At L exit D) :
    Eqv β.toList (Region.br exit (erase t)).bindBranchArguments ((Code.ofLetCase d).guardedSSA exit) L := by
  induction d generalizing L exit with
  | @fv _ _ x => exact x.elim
  | bv => exact reflBr pe .bv hi
  | op d _ => exact reflBr pe (.op d) hi
  | unit => exact reflBr pe .unit hi
  | pair l r _ _ => exact reflBr pe (.pair l r) hi
  | inl l _ => exact reflBr pe (.inl l) hi
  | inr r _ => exact reflBr pe (.inr r) hi
  | abort d _ => exact reflBr pe (.abort d) hi
  | let₂ => exact admitted.elim
  | @let₁ _ β a b A B da db iha ihb =>
    obtain ⟨oka, okb⟩ := admitted
    have ha := erase_hasType da.toHasType
    have hb := erase_hasType db.toHasType
    have e := Paper.UnaryReturn.Step.fuse ha hb
    obtain ⟨l, r⟩ := e.valueBranches
    have fused : Eqv β.toList _ _ [B] := .extra l.hasType r.hasType (.inl e)
    have forward := fused.symm.renameLabels (singletonRen hi)
    have body := ihb okb hi
    have entry := iha oka (rfl : At (A :: L) 0 A)
    have toJoin := letToJoin pe ha (guarded_typed (Code.ofLetCase db) hi) entry
    rw [guarded_rename] at toJoin
    exact forward.trans ((Paper.Extension.Eqv.let₁ ha body).trans toJoin)
  | @case _ β discrTerm leftTerm rightTerm A B D de dl dr ihe ihl ihr =>
    obtain ⟨iface, discr, l, r, hl, hr, le, re⟩ := admitted
    have lvalue : Tm.BranchValue (A :: β.toList) (erase leftTerm) D := by
      rw [le, iface]
      exact value_rename hl ((Ren.wk [] (coprod A B)).lift A)
    have rvalue : Tm.BranchValue (B :: β.toList) (erase rightTerm) D := by
      rw [re, iface]
      exact value_rename hr ((Ren.wk [] (coprod A B)).lift B)
    have lhs := constructor_reifies_as_branch dl lvalue exit
    have rhs := constructor_reifies_as_branch dr rvalue exit
    change Eqv β.toList (Region.br exit (.case (erase discrTerm) (erase leftTerm) (erase rightTerm))).bindBranchArguments
      (.case (erase discrTerm) ((Code.ofLetCase dl).toSSA exit).bindBranchArguments
        ((Code.ofLetCase dr).toSSA exit).bindBranchArguments) L
    rw [lhs, rhs, discr, le, re, iface]
    exact splitReturn pe hl hr hi

include pe in
theorem code {n : Nat} {β : BoundCtx τ n} {A : τ} (c : Code Φ β A)
    (admitted : c.Admitted) {L : LCtx τ} {exit : Nat} (hi : At L exit A) :
    Eqv β.toList (c.guardedSSA exit) ((Code.ofLetCase c.toLetCase.2).guardedSSA exit) L := by
  induction c generalizing L exit with
  | br a => exact operand pe a.2 admitted hi
  | let₁ a body ih =>
    obtain ⟨oka, okb⟩ := admitted
    have ha := erase_hasType a.2.toHasType
    have combined := letToJoin pe ha (guarded_typed (Code.ofLetCase body.toLetCase.2) hi)
      (operand pe a.2 oka rfl)
    rw [guarded_rename] at combined
    exact (Paper.Extension.Eqv.let₁ ha (ih okb hi)).trans combined
  | let₂ a body ih => exact .let₂ (erase_hasType a.2.toHasType) (ih admitted hi)
  | case a left right ihl ihr =>
    exact .case (erase_hasType a.2.toHasType) (ihl admitted.1 hi) (ihr admitted.2 hi)
  | @join _ _ B _ entry body ihe ihb =>
    exact joinCongr pe (ihe admitted.1 (rfl : At (B :: L) 0 B))
      (ihb admitted.2 (exit := exit + 1) (show At (B :: L) (exit + 1) _ from hi))

end Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.SyntacticRoundTrip
