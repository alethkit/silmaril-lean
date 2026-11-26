module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.AdjacentSwap.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.RedundantTest.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.ProductEta.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Endpoint.Thms

/-! # Open adjacent swap by typed packet expansion -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.AdjacentSwap

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open Paper.WithCaseBind.SelectedTerminal (Seed)
open Paper
open Paper.WithCaseBind.OpenReplay

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy
local notation "E" => Paper.Extension.Eqv Seed
local notation "U" => (unit : Ty Empty)
local notation "P₂" => replyContext 2

private def tag (b : Bool) (u : Tm signature.Instr) : Tm signature.Instr :=
  if b then .inr u else .inl u

private def bitBranch (i : Nat) (b : Bool) (j : Nat) : Tm signature.Instr :=
  if j = i then tag b (.var 0) else .var (j + 1)

private theorem bit_ext {Γ L : List (Ty Empty)} {p q : Region signature.Instr} {i : Nat}
    (hi : At Γ i Bit) (hp : HasType Γ p L) (hq : HasType Γ q L)
    (arms : ∀ b, E (U :: Γ) (p.substVars (bitBranch i b)) (q.substVars (bitBranch i b)) L) :
    E Γ p q L := by
  let ρ (j : Nat) := if j = i then 0 else j + 1
  have hρ : Ren Γ (Bit :: Γ) ρ := by
    intro j D hj
    by_cases e : j = i
    · subst j
      have t := Option.some.inj (hj.symm.trans hi)
      subst D
      simp [ρ, At]
    · simpa [ρ, e, At] using hj
  have identity (r : Region signature.Instr) :
      (r.renameVars ρ).substVars (Tm.singleSubst (.var i)) = r := by
    rw [substVars_renameVars]
    have eq : (Tm.singleSubst (.var i) ∘ ρ) = (Tm.var : Nat → Tm signature.Instr) := by
      funext j
      by_cases e : j = i
      · subst j; simp [ρ, Tm.singleSubst, Tm.consSubst]
      · simp [ρ, e, Tm.singleSubst, Tm.consSubst]
    rw [eq, substVars_var]
  have branch (r : Region signature.Instr) (b : Bool) :
      (r.renameVars ρ).substVars (Tm.replaceNewest (tag b (.var 0))) =
        r.substVars (bitBranch i b) := by
    rw [substVars_renameVars]
    congr
    funext j
    by_cases e : j = i <;> simp [ρ, bitBranch, e, Tm.replaceNewest, Tm.consSubst]
  have expand (r : Region signature.Instr) (hr : HasType Γ r L) :
      E Γ (.case (.var i) (r.substVars (bitBranch i false)) (r.substVars (bitBranch i true))) r L := by
    have step := Paper.Extension.Eqv.paper (Seed := Seed) (.cfgEta (.native
      (.caseValue (.var hi) (hr.renameVars hρ))))
    rw [identity] at step
    rw [← branch r false, ← branch r true]
    exact step
  exact (expand p hp).symm.trans ((Paper.Extension.Eqv.case (.var hi) (arms false) (arms true)).trans (expand q hq))

private theorem product_ext {Γ L : List (Ty Empty)} {p q : Region signature.Instr} {i : Nat}
    {A B : Ty Empty} (hi : At Γ i (product A B)) (hp : HasType Γ p L) (hq : HasType Γ q L)
    (pair : E (B :: A :: Γ) (p.substVars (splitProduct i)) (q.substVars (splitProduct i)) L) :
    E Γ p q L :=
  (Paper.Extension.Eqv.paper (product_variable_eta_context hi hp)).symm.trans
    ((Paper.Extension.Eqv.let₂ (.var hi) pair).trans (.paper (product_variable_eta_context hi hq)))

private theorem typeSplit {Γ : List (Ty Empty)} {i : Nat} {A B : Ty Empty}
    (hi : At Γ i (product A B)) :
    Tm.Subst.HasType (Φ := signature.Instr) Γ (B :: A :: Γ) (splitProduct i) := by
  intro j D hj
  by_cases e : j = i
  · subst j
    have t := Option.some.inj (hj.symm.trans hi)
    subst D
    simp only [splitProduct, ↓reduceIte]
    exact .pair (.var (i := 1) rfl) (.var (i := 0) rfl)
  · simp only [splitProduct, e, ↓reduceIte]
    exact .var (by simpa [At] using hj)

private theorem typeBranch {Γ : List (Ty Empty)} {i : Nat} (hi : At Γ i Bit) (b : Bool) :
    Tm.Subst.HasType (Φ := signature.Instr) Γ (U :: Γ) (bitBranch i b) := by
  intro j D hj
  by_cases e : j = i
  · subst j
    have t := Option.some.inj (hj.symm.trans hi)
    subst D
    simp only [bitBranch, ↓reduceIte]
    cases b <;> simp only [tag, Bool.false_eq_true, ↓reduceIte]
    · exact .inl (.var (i := 0) rfl)
    · exact .inr (.var (i := 0) rfl)
  · simp only [bitBranch, e, ↓reduceIte]
    exact .var (by simpa [At] using hj)

private abbrev checkCtx : List (Ty Empty) :=
  [U, U, Bit, U, Bit, product U Bit, P₂]

private def taggedPacket (older newer : Bool) : Tm signature.Instr :=
  .pair (.pair (.var 3) (tag older (.var 1))) (tag newer (.var 0))

private theorem packet_ext {L : List (Ty Empty)} {p q : Region signature.Instr}
    (hp : HasType [P₂] p L) (hq : HasType [P₂] q L)
    (rows : ∀ older newer, E checkCtx
      (p.substVars (Tm.singleSubst (taggedPacket older newer)))
      (q.substVars (Tm.singleSubst (taggedPacket older newer))) L) :
    E [P₂] p q L := by
  have hOuter : At [P₂] 0 (product (product U Bit) Bit) := rfl
  have hInner : At [Bit, product U Bit, P₂] 1 (product U Bit) := rfl
  have hOlder : At [Bit, U, Bit, product U Bit, P₂] 0 Bit := rfl
  have hNewer : At [U, Bit, U, Bit, product U Bit, P₂] 3 Bit := rfl
  apply product_ext hOuter hp hq
  let pp := hp.substVars (typeSplit hOuter)
  let qq := hq.substVars (typeSplit hOuter)
  apply product_ext hInner pp qq
  let pp := pp.substVars (typeSplit hInner)
  let qq := qq.substVars (typeSplit hInner)
  apply bit_ext hOlder pp qq
  intro older
  apply bit_ext hNewer (pp.substVars (typeBranch hOlder older)) (qq.substVars (typeBranch hOlder older))
  intro newer
  simp only [substVars_comp]
  rw [Paper.SingletonReification.SingleCfg.singleton_subst hp
    (υ := Tm.singleSubst (taggedPacket older newer)) (by cases older <;> cases newer <;> rfl)]
  rw [Paper.SingletonReification.SingleCfg.singleton_subst hq
    (υ := Tm.singleSubst (taggedPacket older newer)) (by cases older <;> cases newer <;> rfl)]
  exact rows older newer

theorem selected_adjacent_swap {L : List (Ty Empty)} (pos : Position L) (bits : List Bool)
    (table : Finite.Table 2) :
    selectedEq (selectTerminal pos (Finite.Expr.quote 2 table) (readReply 2) bits)
      (selectTerminal pos (Finite.Expr.quote 2 (fun row => table (row ∘ Fin.rev)))
        (readReply 2 ∘ Fin.rev) bits) := by
  let reversed := fun row : Finite.Assignment 2 => table (row ∘ Fin.rev)
  let left := selectTerminal pos (Finite.Expr.quote 2 table) (readReply 2) []
  let right := selectTerminal pos (Finite.Expr.quote 2 reversed) (readReply 2 ∘ Fin.rev) []
  have bare : selectedEq left right := by
    apply packet_ext left.elaborate.property.hasType right.elaborate.property.hasType
    intro older newer
    let earlier : Tm.BranchValue checkCtx (.var 3 : Tm signature.Instr) U := .var (i := 3) rfl
    let leftUnit : Tm.BranchValue checkCtx (.var 1 : Tm signature.Instr) U := .var (i := 1) rfl
    let rightUnit : Tm.BranchValue checkCtx (.var 0 : Tm signature.Instr) U := .var (i := 0) rfl
    have normal := quoted_packet pos table id older newer earlier leftUnit rightUnit
    have swapped := quoted_packet pos reversed Fin.rev older newer earlier leftUnit rightUnit
    have twice : ((Fin.cases newer (fun _ => older) : Finite.Assignment 2) ∘ Fin.rev) ∘ Fin.rev =
        Fin.cases newer (fun _ => older) := by
      funext j
      simp only [Function.comp_apply, Fin.rev_rev]
    dsimp only [reversed] at swapped
    simp only [twice] at swapped
    exact normal.trans swapped.symm
  exact (terminal_prefix (Finite.Expr.quote 2 table) pos (readReply 2) bits).trans
    ((prependEmits_congr bits bare).trans
      (terminal_prefix (Finite.Expr.quote 2 reversed) pos (readReply 2 ∘ Fin.rev) bits).symm)

theorem packed_adjacent_swap {L : List (Ty Empty)} (pos : Position L) (bits : List Bool)
    (table : Finite.Table 2) :
    packed (.retExpr bits pos (Finite.Expr.quote 2 table)) =
      packedTable pos bits (fun row => table (row ∘ Fin.rev)) Fin.rev := by
  let l := selectTerminal pos (Finite.Expr.quote 2 table) (readReply 2) bits
  let r := selectTerminal pos (Finite.Expr.quote 2 (fun row => table (row ∘ Fin.rev)))
    (readReply 2 ∘ Fin.rev) bits
  apply (Paper.Extension.Singleton.ofRegion_eq_iff Seed _ _).2
  exact (selected_adjacent_swap pos bits table).lsubstPost l.elaborate.property r.elaborate.property
    (fun _ _ hi => (packExits_valueFamily _ L hi).hasType)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.AdjacentSwap
