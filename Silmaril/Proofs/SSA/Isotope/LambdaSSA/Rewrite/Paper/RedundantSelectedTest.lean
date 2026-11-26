module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.RedundantTest.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Discard.Syntax.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.Normalization.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Projection.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Endpoint.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms

/-! # Weakening and emit factoring for one redundant selected test -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RedundantSelectedTest

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open Paper.WithCaseBind.SelectedTerminal (Seed)
open Paper.WithCaseBind.OpenReplay
open CfgEta.TypeCategory (returnRegion returnRegion_typed singletonValueFamily)
open Paper.RetainedLet (returnOnce)
open Paper.UnaryReturn (returnOnce_valueBranches)
open Silmaril.DeBruijn (lift)

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

local notation "E" => Paper.Extension.Eqv Seed

private theorem inclUnary {Γ L r s} (h : Paper.UnaryReturn.Step Γ r s L) : Seed Γ r s L :=
  .inl (.inl (.inr (.inl h)))

private theorem inclPair {Γ L r s} (h : Paper.WithPairReturns.Step Γ r s L) : Seed Γ r s L :=
  .inl (.inr h)

private theorem inclProjection {Γ L r s} (h : Paper.WithProjectionReturns.Step Γ r s L) : Seed Γ r s L :=
  .inl (.inl (.inl (.inl h)))

private theorem oncePost (a : Tm signature.Instr) (r : Region signature.Instr) :
    (returnOnce a).lsubst (fun _ => r) = .let₁ a r := by
  change Region.let₁ a (compLSubst labelId (fun _ => r) 0) = _
  rw [compLSubst_id_left]

private theorem prefix_congr {Γ L : List (Ty Empty)} {r s : Region signature.Instr}
    (bits : List Bool) (h : E Γ r s L) : E Γ (prependEmits bits r) (prependEmits bits s) L := by
  induction bits with
  | nil => exact h
  | cons b bs ih => exact .let₁ (.op .unit) (ih.renameVars (Ren.wk Γ unit))

private theorem prefix_lsubst (bits : List Bool) (r : Region signature.Instr) (σ : Nat → Region signature.Instr) :
    (prependEmits bits r).lsubst σ = prependEmits bits (r.lsubst σ) := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    simp only [prependEmits, lsubst, ← ih]
    exact congrArg (Region.let₁ (.op (show signature.Instr from Op.emit b) .unit))
      (renameVars_lsubst (prependEmits bs r) σ Nat.succ).symm

private theorem prefix_return {X D : Ty Empty} (bits : List Bool) (t : Term signature.Instr X D) :
    E [X] (returnRegion (emitPrefix bits t).elaborate.val)
      (prependEmits bits (returnRegion t.elaborate.val)) [D] := by
  induction bits with
  | nil => exact .refl (returnRegion_typed t.elaborate.property).hasType
  | cons b bs ih =>
    let ha : Tm.HasType [X] (.op (show signature.Instr from Op.emit b) .unit) unit := .op .unit
    let hb := (emitPrefix bs t).elaborate.property
    have pair := Paper.WithPairReturns.return_pair_second inclPair inclProjection ha hb
    have lower := (Paper.UnaryReturn.returnRegion_eq_returnOnce inclUnary hb).symm.trans ih
    exact pair.trans (.let₁ ha (lower.renameVars (Ren.wk [X] unit)))

private theorem prefix_post {X D : Ty Empty} {L : List (Ty Empty)}
    (bits : List Bool) (t : Term signature.Instr X D) {k r : Region signature.Instr}
    (hk : ValueBranches [D, X] k L)
    (tail : E [X] ((returnRegion t.elaborate.val).lsubst (fun _ => k)) r L) :
    E [X] ((returnRegion (emitPrefix bits t).elaborate.val).lsubst (fun _ => k))
      (prependEmits bits r) L := by
  have moved := (prefix_return bits t).lsubstPost (returnRegion_typed (emitPrefix bits t).elaborate.property)
    (by
      induction bits with
      | nil => exact returnRegion_typed t.elaborate.property
      | cons b bs ih => exact .let₁ (.op .unit) (ih.renameVars (Ren.wk [X] unit)))
    (fun _ _ hi => by
      have eq : _ = D := List.mem_singleton.mp (List.mem_of_getElem? hi)
      exact eq.symm ▸ hk.hasType)
  rw [prefix_lsubst] at moved
  exact moved.trans (prefix_congr bits tail)

private theorem constructorSubst {Γ : VCtx (Ty Empty)} {X : Ty Empty} {a : Tm signature.Instr}
    (ha : Tm.BranchValue Γ a X) :
    ∀ ⦃i A⦄, At [X] i A → Tm.BranchValue Γ (Tm.singleSubst a i) A := by
  intro i A hi
  cases i with
  | zero => cases Option.some.inj hi; exact ha
  | succ i => simp [At] at hi

private theorem term_singleton_subst {X D : Ty Empty} {a : Tm signature.Instr}
    (ha : Tm.HasType [X] a D) {θ σ : Nat → Tm signature.Instr}
    (h : θ 0 = σ 0) : a.subst θ = a.subst σ :=
  (Region.br.inj (Paper.SingletonReification.SingleCfg.singleton_subst (L := [D])
    (.br (ℓ := 0) rfl ha) h)).2

private theorem open_packed_arm {X A : Ty Empty} {L : List (Ty Empty)}
    {r : Region signature.Instr} {a : Tm signature.Instr}
    (hr : HasType [product X A] r L) :
    (Paper.PackedBody.applyPacked r).substVars (Tm.liftSubst (Tm.singleSubst a)) =
      r.substVars (Tm.singleSubst (.pair (a.rename Nat.succ) (.var 0))) := by
  rw [Paper.PackedBody.applyPacked, substVars_comp]
  exact Paper.SingletonReification.SingleCfg.singleton_subst hr rfl

private theorem retained_returnOnce {Γ : VCtx (Ty Empty)} {X A : Ty Empty}
    (t : Term signature.Instr X Bit) {a b : Tm signature.Instr}
    (ha : Tm.BranchValue Γ a X) (hb : Tm.BranchValue Γ b A) :
    E Γ (returnOnce ((retainSlot (A := A) t).elaborate.val.subst (Tm.singleSubst (.pair a b))))
      (returnOnce (t.elaborate.val.subst (Tm.singleSubst a))) [Bit] := by
  let projection := Paper.WithProjectionReturns.Step.fst (Φ := signature.Instr) X A
  have proj : E [product X A] (returnOnce (.let₂ (.var 0) (.var 1))) (.let₂ (.var 0) (.br 0 (.var 1))) [X] :=
    .extra projection.valueBranches.1.hasType projection.valueBranches.2.hasType (inclProjection projection)
  have first : E Γ (returnOnce (.let₂ (.pair a b) (.var 1))) (.br 0 a) [X] :=
    (proj.substVars (constructorSubst (.pair ha hb))).trans
      (.paper (.productBeta (.let₂Beta ha hb (.br rfl (.var (i := 1) rfl)))))
  let body := (t.elaborate.val.rename (lift Nat.succ)).subst (Tm.liftSubst (Tm.singleSubst (.pair a b)))
  have hpair : Tm.Subst.HasType [product X A] Γ (Tm.singleSubst (.pair a b)) :=
    fun _ _ hi => (constructorSubst (.pair ha hb) hi).hasType
  have hbody : Tm.HasType (X :: Γ) body Bit :=
    (t.elaborate.property.rename ((Ren.wk [] (product X A)).lift X)).subst (hpair.lift X)
  let hfst : Tm.HasType Γ (.let₂ (.pair a b) (.var 1)) X := .let₂ (.pair ha.hasType hb.hasType) (.var (i := 1) rfl)
  let fuse := Paper.UnaryReturn.Step.fuse hfst hbody
  have commute : E Γ (.let₁ (.let₂ (.pair a b) (.var 1)) (returnOnce body))
      (returnOnce ((retainSlot (A := A) t).elaborate.val.subst (Tm.singleSubst (.pair a b)))) [Bit] :=
    .extra fuse.valueBranches.1.hasType fuse.valueBranches.2.hasType (inclUnary fuse)
  have continued := first.lsubstPost (returnOnce_valueBranches hfst) (.br rfl ha)
    (fun _ _ hi => ((singletonValueFamily (returnOnce_valueBranches hbody)) hi).hasType)
  rw [oncePost] at continued
  have eq : body.subst (Tm.singleSubst a) = t.elaborate.val.subst (Tm.singleSubst a) := by
    unfold body
    simp only [Tm.subst_rename, Tm.subst_comp]
    exact term_singleton_subst t.elaborate.property rfl
  change E Γ _ (returnOnce (body.subst (Tm.singleSubst a))) [Bit] at continued
  exact commute.symm.trans (eq ▸ continued)

private theorem case_congr_returnOnce {Γ L : List (Ty Empty)} {a b : Tm signature.Instr}
    {l r : Region signature.Instr} (ha : Tm.HasType Γ a Bit) (hb : Tm.HasType Γ b Bit)
    (hl : ValueBranches (unit :: Γ) l L) (hr : ValueBranches (unit :: Γ) r L)
    (eq : E Γ (returnOnce a) (returnOnce b) [Bit]) :
    E Γ (.case a l r) (.case b l r) L := by
  let k := Paper.RetainedCase.boundCase_typed hl hr
  have post : LSubst.HasType Γ [Bit] L (fun _ => Paper.RetainedCase.boundCase l r) :=
    fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ k.hasType
  have bind := eq.lsubstPost (returnOnce_valueBranches ha) (returnOnce_valueBranches hb) post
  rw [oncePost, oncePost] at bind
  exact (Paper.WithCaseBind.case_eq_let Or.inr ha hl hr).trans
    (bind.trans (Paper.WithCaseBind.case_eq_let Or.inr hb hl hr).symm)

private theorem weaken_value {Γ : VCtx (Ty Empty)} {X : Ty Empty} {a : Tm signature.Instr}
    (ha : Tm.BranchValue Γ a X) : Tm.BranchValue (unit :: Γ) (a.rename Nat.succ) X := by
  rw [Tm.rename_eq_subst]
  exact ha.subst (fun _ _ h => .var (Ren.wk Γ unit h))

private theorem slot_return_rename {X : Ty Empty} (t : Term signature.Instr X Bit) (a : Tm signature.Instr) :
    ((t.elaborate.val.subst (Tm.singleSubst a)).rename Nat.succ) =
      t.elaborate.val.subst (Tm.singleSubst (a.rename Nat.succ)) := by
  rw [Tm.rename_subst]
  exact term_singleton_subst t.elaborate.property rfl

set_option backward.isDefEq.respectTransparency false in
private theorem terminal_subst_congr {n : Nat} {L : List (Ty Empty)}
    (e : Finite.Expr n) (pos : Position L) {Γ : VCtx (Ty Empty)} {X Y : Ty Empty}
    (left : Fin n → Term signature.Instr X Bit) (right : Fin n → Term signature.Instr Y Bit)
    {a b : Tm signature.Instr} (ha : Tm.BranchValue Γ a X) (hb : Tm.BranchValue Γ b Y)
    (slot : ∀ i,
      E Γ (returnOnce ((left i).elaborate.val.subst (Tm.singleSubst a)))
        (returnOnce ((right i).elaborate.val.subst (Tm.singleSubst b))) [Bit]) :
    E Γ ((selectTerminal pos e left []).elaborate.val.substVars (Tm.singleSubst a))
      ((selectTerminal pos e right []).elaborate.val.substVars (Tm.singleSubst b)) L := by
  induction e generalizing Γ X Y a b with
  | literal bit =>
    cases bit
    · exact .refl (.let₁ .unit (.br pos.typed (.inl (.var (i := 0) rfl))))
    · exact .refl (.let₁ .unit (.br pos.typed (.inr (.var (i := 0) rfl))))
  | read i =>
    have el := (Paper.UnaryReturn.returnRegion_eq_returnOnce inclUnary (left i).elaborate.property).substVars
      (constructorSubst ha)
    have er := (Paper.UnaryReturn.returnRegion_eq_returnOnce inclUnary (right i).elaborate.property).substVars
      (constructorSubst hb)
    change E Γ ((returnRegion (left i).elaborate.val).renameLabels (fun _ => pos.1) |>.substVars (Tm.singleSubst a))
      ((returnRegion (right i).elaborate.val).renameLabels (fun _ => pos.1) |>.substVars (Tm.singleSubst b)) L
    rw [substVars_renameLabels, substVars_renameLabels]
    exact (el.trans ((slot i).trans er.symm)).renameLabels (singletonExitRen pos.typed)
  | split low high il ir =>
    let leftOlder := fun (i : Fin _) => retainSlot (A := unit) (left i.succ)
    let rightOlder := fun (i : Fin _) => retainSlot (A := unit) (right i.succ)
    let al := (.pair (weaken_value ha) (.var (i := 0) rfl) :
      Tm.BranchValue (unit :: Γ) (.pair (a.rename Nat.succ) (.var 0)) (product X unit))
    let br := (.pair (weaken_value hb) (.var (i := 0) rfl) :
      Tm.BranchValue (unit :: Γ) (.pair (b.rename Nat.succ) (.var 0)) (product Y unit))
    have older (i : Fin _) :
        E (unit :: Γ)
          (returnOnce ((leftOlder i).elaborate.val.subst (Tm.singleSubst (.pair (a.rename Nat.succ) (.var 0)))))
          (returnOnce ((rightOlder i).elaborate.val.subst (Tm.singleSubst (.pair (b.rename Nat.succ) (.var 0))))) [Bit] := by
      have weakened := (slot i.succ).renameVars (Ren.wk Γ unit)
      change E (unit :: Γ)
        (returnOnce (((left i.succ).elaborate.val.subst (Tm.singleSubst a)).rename Nat.succ))
        (returnOnce (((right i.succ).elaborate.val.subst (Tm.singleSubst b)).rename Nat.succ)) [Bit] at weakened
      rw [slot_return_rename, slot_return_rename] at weakened
      exact (retained_returnOnce (left i.succ) (weaken_value ha) (.var (i := 0) rfl)).trans
        (weakened.trans (retained_returnOnce (right i.succ) (weaken_value hb) (.var (i := 0) rfl)).symm)
    let ls := (selectTerminal pos low leftOlder []).elaborate
    let rs := (selectTerminal pos high leftOlder []).elaborate
    let ls' := (selectTerminal pos low rightOlder []).elaborate
    let rs' := (selectTerminal pos high rightOlder []).elaborate
    have eqL := il leftOlder rightOlder al br older
    have eqR := ir leftOlder rightOlder al br older
    change E Γ
      (.case ((left 0).elaborate.val.subst (Tm.singleSubst a))
        ((Paper.PackedBody.applyPacked ls.val).substVars (Tm.liftSubst (Tm.singleSubst a)))
        ((Paper.PackedBody.applyPacked rs.val).substVars (Tm.liftSubst (Tm.singleSubst a))))
      (.case ((right 0).elaborate.val.subst (Tm.singleSubst b))
        ((Paper.PackedBody.applyPacked ls'.val).substVars (Tm.liftSubst (Tm.singleSubst b)))
        ((Paper.PackedBody.applyPacked rs'.val).substVars (Tm.liftSubst (Tm.singleSubst b)))) L
    rw [open_packed_arm ls.property.hasType, open_packed_arm rs.property.hasType,
      open_packed_arm ls'.property.hasType, open_packed_arm rs'.property.hasType]
    let lty := ls.property.substVars (constructorSubst al)
    let rty := rs.property.substVars (constructorSubst al)
    let hleft := (left 0).elaborate.property.subst (fun _ _ hi => (constructorSubst ha hi).hasType)
    let hright := (right 0).elaborate.property.subst (fun _ _ hi => (constructorSubst hb hi).hasType)
    exact (case_congr_returnOnce hleft hright lty rty (slot 0)).trans (.case hright eqL eqR)

theorem terminal_weakening {X : Ty Empty} {L : List (Ty Empty)} {n : Nat}
    (e : Finite.Expr n) (pos : Position L) (slots : Fin n → Term signature.Instr X Bit) :
    E [unit, X]
      (Paper.PackedBody.applyPacked (selectTerminal pos e (fun i => retainSlot (A := unit) (slots i)) []).elaborate.val)
      ((selectTerminal pos e slots []).elaborate.val.renameVars Nat.succ) L := by
  let a : Tm.BranchValue [unit, X] (.var 1 : Tm signature.Instr) X := .var (i := 1) rfl
  let u : Tm.BranchValue [unit, X] (.var 0 : Tm signature.Instr) unit := .var (i := 0) rfl
  have eq := terminal_subst_congr e pos (fun i => retainSlot (A := unit) (slots i)) slots
    (.pair a u) a (fun i => retained_returnOnce (slots i) a u)
  unfold Paper.PackedBody.applyPacked
  rw [renameVars_eq_substVars]
  have left := Paper.SingletonReification.SingleCfg.singleton_subst
    (selectTerminal pos e (fun i => retainSlot (A := unit) (slots i)) []).elaborate.property.hasType
    (θ := Tm.consSubst (.pair (.var 1) (.var 0)) (Tm.var ∘ (Nat.succ ∘ Nat.succ)))
    (υ := Tm.singleSubst (.pair (.var 1) (.var 0))) rfl
  have right := Paper.SingletonReification.SingleCfg.singleton_subst (selectTerminal pos e slots []).elaborate.property.hasType
    (θ := Tm.var ∘ Nat.succ) (υ := Tm.singleSubst (.var 1)) rfl
  rw [left, right]
  exact eq

private theorem lower_binding {X D : Ty Empty} {L : List (Ty Empty)}
    {a : Tm signature.Instr} {r : Region signature.Instr}
    (ha : Tm.HasType [X] a D) (hr : ValueBranches [D, X] r L) :
    E [X] (.let₁ a r) ((returnRegion a).lsubst (fun _ => r)) L := by
  have eq := (Paper.UnaryReturn.returnRegion_eq_returnOnce inclUnary ha).lsubstPost
    (returnRegion_typed ha) (returnOnce_valueBranches ha)
    (fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ hr.hasType)
  rw [oncePost] at eq
  exact eq.symm

private theorem prefix_binding {X D : Ty Empty} {L : List (Ty Empty)}
    (bits : List Bool) (t : Term signature.Instr X D)
    {r : Region signature.Instr} (hr : ValueBranches [D, X] r L) :
    E [X] (.let₁ (emitPrefix bits t).elaborate.val r)
      (prependEmits bits (.let₁ t.elaborate.val r)) L :=
  (lower_binding (emitPrefix bits t).elaborate.property hr).trans
    (prefix_post bits t hr (lower_binding t.elaborate.property hr).symm)

private theorem prefix_case {X : Ty Empty} {L : List (Ty Empty)}
    (bits : List Bool) (t : Term signature.Instr X Bit)
    {l r : Region signature.Instr} (hl : ValueBranches [unit, X] l L) (hr : ValueBranches [unit, X] r L) :
    E [X] (.case (emitPrefix bits t).elaborate.val l r)
      (prependEmits bits (.case t.elaborate.val l r)) L :=
  (Paper.WithCaseBind.case_eq_return_post Or.inr inclUnary (emitPrefix bits t).elaborate.property hl hr).trans
    (prefix_post bits t (Paper.RetainedCase.boundCase_typed hl hr)
      (Paper.WithCaseBind.case_eq_return_post Or.inr inclUnary t.elaborate.property hl hr).symm)

theorem terminal_prefix {X : Ty Empty} {L : List (Ty Empty)} {n : Nat}
    (e : Finite.Expr n) (pos : Position L) (slots : Fin n → Term signature.Instr X Bit) (bits : List Bool) :
    E [X] (selectTerminal pos e slots bits).elaborate.val
      (prependEmits bits (selectTerminal pos e slots []).elaborate.val) L := by
  cases e with
  | literal b =>
    cases b
    · exact prefix_binding bits .unit (.br pos.typed (.inl (.var (i := 0) rfl)))
    · exact prefix_binding bits .unit (.br pos.typed (.inr (.var (i := 0) rfl)))
  | read i =>
    let t := slots i
    change E [X] ((returnRegion (emitPrefix bits t).elaborate.val).renameLabels (fun _ => pos.1))
      (prependEmits bits ((returnRegion t.elaborate.val).renameLabels (fun _ => pos.1))) L
    simp only [renameLabels_eq_lsubst]
    let k : Region signature.Instr := .br pos.1 (.var 0)
    have hk : ValueBranches [Bit, X] k L := .br pos.typed (.var (i := 0) rfl)
    change E [X] ((returnRegion (emitPrefix bits t).elaborate.val).lsubst (fun _ => k))
      (prependEmits bits ((returnRegion t.elaborate.val).lsubst (fun _ => k))) L
    have hpost : LSubst.HasType [X] [Bit] L (fun _ => k) :=
      fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ hk.hasType
    have ht := (returnRegion_typed t.elaborate.property).hasType.lsubst hpost
    exact prefix_post bits t hk (.refl ht)
  | split low high =>
    let older := fun (i : Fin _) => retainSlot (A := unit) (slots i.succ)
    exact prefix_case bits (slots 0)
      (applyPacked_typed_exits (selectTerminal pos low older []).elaborate.property)
      (applyPacked_typed_exits (selectTerminal pos high older []).elaborate.property)

theorem redundant_test {X : Ty Empty} {L : List (Ty Empty)} {n : Nat}
    (e : Finite.Expr n) (pos : Position L) (slots : Fin (n + 1) → Term signature.Instr X Bit)
    (bits : List Bool) (drop : Paper.Extension.ReturnDiscards Seed [X] (slots 0).elaborate.val) :
    selectedEq (selectTerminal pos (.split e e) slots bits)
      (selectTerminal pos e (fun i => slots i.succ) bits) := by
  let tail := (selectTerminal pos e (fun i => slots i.succ) []).elaborate
  have weaken := terminal_weakening e pos (fun i => slots i.succ)
  have arms := Paper.Extension.Eqv.case (slots 0).elaborate.property weaken weaken
  have skip := Paper.WithCaseBind.case_eq_of_returnDiscards Or.inr inclUnary
    (slots 0).elaborate.property tail.property drop
  exact (terminal_prefix (.split e e) pos slots bits).trans
    ((prefix_congr bits (arms.trans skip)).trans (terminal_prefix e pos (fun i => slots i.succ) bits).symm)

theorem snd_discards (X D : Ty Empty) :
    Paper.Extension.ReturnDiscards Seed [product X D] (Term.snd (Φ := signature.Instr) X D).elaborate.val := by
  let projection := Paper.WithProjectionReturns.Step.snd (Φ := signature.Instr) X D
  have eq : E [product X D] (returnRegion (.let₂ (.var 0) (.var 0)))
      (.let₂ (.var 0) (.br 0 (.var 0))) [D] :=
    .extra projection.valueBranches.1.hasType projection.valueBranches.2.hasType (inclProjection projection)
  have drop : LSubst.HasType (Φ := signature.Instr) [product X D] [D] [unit] (fun _ => .br 0 .unit) :=
    fun _ _ _ => .br rfl .unit
  have discard := eq.lsubstPost projection.valueBranches.1 projection.valueBranches.2 drop
  have eta : E [product X D] (.let₂ (.var 0) (.br 0 (.pair (.var 1) (.var 0))))
      (.br 0 (.var 0)) [product X D] :=
    .paper (.productEta (.let₂Eta (i := 0) (ℓ := 0) rfl rfl))
  have pairTyped : ValueBranches (Φ := signature.Instr) [product X D]
      (.let₂ (.var 0) (.br 0 (.pair (.var 1) (.var 0))))
      [product X D] := .let₂ (.var (i := 0) rfl) (.br rfl (.pair (.var (i := 1) rfl) (.var (i := 0) rfl)))
  exact discard.trans (eta.lsubstPost pairTyped (.br rfl (.var (i := 0) rfl)) (fun _ _ _ => .br rfl .unit))

theorem second_quote {X : Ty Empty} {L : List (Ty Empty)}
    (pos : Position L) (slots : Fin 2 → Term signature.Instr X Bit) (bits : List Bool)
    (drop : Paper.Extension.ReturnDiscards Seed [X] (slots 0).elaborate.val) :
    selectedEq (selectTerminal pos (.read 1) slots bits)
      (selectTerminal pos (Finite.Expr.quote 2 (fun env => env 1)) slots bits) :=
  (Paper.WithCaseBind.OpenReplay.newest_eq bits pos (fun i : Fin 1 => slots i.succ)).trans
    (redundant_test (newestTable 0) pos slots bits drop).symm

theorem packed_second_quote {L : List (Ty Empty)} (pos : Position L) (bits : List Bool) :
    packed (.ret (n := 2) bits pos 1) = packed (.retExpr bits pos (Finite.Expr.quote 2 (fun env => env 1))) :=
  Paper.WithCaseBind.OpenReplay.packed_congr
    (second_quote pos (readReply 2) bits (snd_discards (replyContext 1) Bit))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RedundantSelectedTest
