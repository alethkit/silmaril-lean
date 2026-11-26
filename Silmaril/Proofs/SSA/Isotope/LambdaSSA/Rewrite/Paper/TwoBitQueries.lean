module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.TwoRequests.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Thms

import Silmaril.SSA.Isotope.LetIter.Categorical.Case.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Substitution.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TwoBitQueries

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseBind.BitQuery Paper.WithCaseBind.BitQuery.TwoRequests
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit answer)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite (Expr Assignment)

local notation "U" => (Ty.unit : Ty Empty)
local notation "E" => Paper.Extension.Eqv Seed

private theorem weaken_subst (t : Tm signature.Instr) (σ : Nat → Tm signature.Instr) :
    (t.rename Nat.succ).subst (Tm.liftSubst σ) = (t.subst σ).rename Nat.succ := by
  rw [Tm.subst_rename, Tm.rename_subst]
  rfl

private theorem compile_subst (label : Bool) {n : Nat} (e : Expr n)
    (slots : Fin n → Tm signature.Instr) (σ : Nat → Tm signature.Instr) :
    (compile label e slots).substVars σ = compile label e (fun i => (slots i).subst σ) := by
  induction e generalizing σ with
  | literal b => cases b <;> rfl
  | read i => rfl
  | split l r ihl ihr =>
    simp only [compile, Region.substVars, ihl, ihr, weaken_subst]

private theorem case_constructor {Γ : VCtx (Ty Empty)} {a : Tm signature.Instr}
    {l r : Region signature.Instr} (b : Bool) (ha : Tm.HasType Γ a U)
    (hl : ValueBranches (U :: Γ) l Exits) (hr : ValueBranches (U :: Γ) r Exits) :
    E Γ (.case (constructorBit b a) l r) (.let₁ a (if b then r else l)) Exits := by
  cases b
  · exact .paper (.cfgEta (.native (.base (.caseInl ha hl.hasType hr.hasType))))
  · exact .paper (.cfgEta (.native (.base (.caseInr ha hl.hasType hr.hasType))))

private theorem drop_call_binder {Γ : VCtx (Ty Empty)} {a : Tm signature.Instr}
    (ha : Tm.BranchValue Γ a U) (label b : Bool) :
    E Γ (.let₁ a (call label (literal b))) (call label (literal b)) Exits := by
  cases b <;> exact .paper (.cfgEta (.native (.letValue ha
    (call_typed label (constructorBit_value _ .unit).hasType).hasType)))

private theorem compile_known (label : Bool) {n : Nat} (e : Expr n) (env : Assignment n)
    {Γ : VCtx (Ty Empty)} (payload : Fin n → Tm signature.Instr)
    (hp : ∀ i, Tm.BranchValue Γ (payload i) U) :
    E Γ (compile label e (fun i => constructorBit (env i) (payload i)))
      (call label (literal (e.eval env))) Exits := by
  induction e generalizing Γ with
  | literal b => exact .refl (call_typed label (constructorBit_value b .unit).hasType).hasType
  | read i =>
    refine (case_constructor (env i) (hp i).hasType
      (call_typed label (.inl .unit)) (call_typed label (.inr .unit))).trans ?_
    cases eq : env i
    · simp only [Expr.eval, eq, Bool.false_eq_true, ite_false]
      exact drop_call_binder (hp i) label false
    · simp only [Expr.eval, eq, ite_true]
      exact drop_call_binder (hp i) label true
  | @split n l r ihl ihr =>
    let older := fun (i : Fin n) => (payload i.succ).rename Nat.succ
    have ht (i) : Tm.BranchValue (U :: Γ) (older i) U := by
      unfold older
      rw [Tm.rename_eq_subst]
      exact (hp i.succ).subst (fun _ _ hi => .var (Ren.wk Γ U hi))
    have rename (i) : (constructorBit (env i.succ) (payload i.succ)).rename Nat.succ =
        constructorBit (env.tail i) (older i) := by
      change (constructorBit (env i.succ) (payload i.succ)).rename Nat.succ =
        constructorBit (env i.succ) ((payload i.succ).rename Nat.succ)
      cases env i.succ <;> rfl
    simp only [compile, rename]
    refine (case_constructor (env 0) (hp 0).hasType
      (compile_typed _ _ (fun i => (constructorBit_value _ (ht i)).hasType))
      (compile_typed _ _ (fun i => (constructorBit_value _ (ht i)).hasType))).trans ?_
    cases h : env 0
    · simpa only [Expr.eval, h, Bool.false_eq_true, ite_false] using
        (Paper.Extension.Eqv.let₁ (hp 0).hasType (ihl env.tail older ht)).trans
          (drop_call_binder (hp 0) label (l.eval env.tail))
    · simpa only [Expr.eval, h, ite_true] using
        (Paper.Extension.Eqv.let₁ (hp 0).hasType (ihr env.tail older ht)).trans
          (drop_call_binder (hp 0) label (r.eval env.tail))

private def beforeReplyCase (guard : Bool) : Fin 2 → Tm signature.Instr :=
  Fin.cases (.var 0) (fun _ => constructorBit guard (.var 2))

private def knownPayloads : Fin 2 → Tm signature.Instr :=
  Fin.cases (.var 0) (fun _ => .var 2)

private theorem extract_query (label : Bool) (e : Expr 2) (guard reply : Bool) :
    E [U, Bit, U, Bit]
      ((compile label e (beforeReplyCase guard)).substVars
        (Tm.replaceNewest (constructorBit reply (.var 0))))
      (call label (literal (e.eval (assignment guard reply)))) Exits := by
  rw [compile_subst]
  have slots : (fun i => (beforeReplyCase guard i).subst
      (Tm.replaceNewest (constructorBit reply (.var 0)))) =
      (fun i => constructorBit (assignment guard reply i) (knownPayloads i)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · cases reply <;> rfl
    · rw [Fin.eq_zero j]
      cases guard <;> rfl
  rw [slots]
  exact compile_known label e (assignment guard reply) knownPayloads
    (fun i => Fin.cases (.var (i := 0) rfl) (fun _ => .var (i := 2) rfl) i)

private theorem replay_row (p : Program) (guard : Bool) :
    E [Bit, U, Bit]
      (compile p.secondLabel p.secondQuery (guardedSlots guard))
      (compile p.secondLabel (p.key.row guard) replySlot) Exits := by
  let body := compile p.secondLabel p.secondQuery (beforeReplyCase guard)
  have ht : ValueBranches [Bit, Bit, U, Bit] body Exits :=
    compile_typed _ _ (fun i => Fin.cases (.var (i := 0) rfl)
      (fun _ => (constructorBit_value guard (.var (i := 2) rfl)).hasType) i)
  have unroll : E [Bit, U, Bit]
      (.case (.var 0)
        (body.substVars (Tm.replaceNewest (constructorBit false (.var 0))))
        (body.substVars (Tm.replaceNewest (constructorBit true (.var 0)))))
      (body.substVars (Tm.singleSubst (.var 0))) Exits :=
    .paper (.cfgEta (.native (.caseValue (.var (i := 0) rfl) ht.hasType)))
  have reduced : body.substVars (Tm.singleSubst (.var 0)) =
      compile p.secondLabel p.secondQuery (guardedSlots guard) := by
    unfold body
    rw [compile_subst]
    congr 1
    funext i
    refine Fin.cases rfl (fun _ => ?_) i
    cases guard <;> rfl
  rw [reduced] at unroll
  exact unroll.symm.trans (.case (.var (i := 0) rfl)
    (extract_query p.secondLabel p.secondQuery guard false)
    (extract_query p.secondLabel p.secondQuery guard true))

theorem packed_replay (p : Program) : p.packed = p.key.packed := by
  have step (guard : Bool) : E [U, Bit]
      (first p.firstLabel guard (compile p.secondLabel p.secondQuery (guardedSlots guard)))
      (first p.firstLabel guard (compile p.secondLabel (p.key.row guard) replySlot)) Exits :=
    .case (.op (constructorBit_value guard .unit).hasType) (replay_row p guard) (replay_row p guard)
  have eq : E [Bit] p.region p.key.region Exits :=
    .case (.var (i := 0) rfl) (step false) (step true)
  exact (Paper.Extension.Singleton.ofRegion_eq_iff Seed _ _).mpr
    (eq.lsubstPost p.typed p.key.typed (fun _ _ hi =>
      (packExits_valueFamily (Φ := signature.Instr) [Bit] Exits hi).hasType))

open CategoryTheory CategoryTheory.Limits
open Semantics.Categorical
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext_of)
open Silmaril.Isotope.LetIter.Semantics.Categorical (case_postcomp InstructionModel)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Answer)
open Silmaril.Semantics.NondeterministicTrace (Tagged)
open scoped MonoidalCategory

local notation "J" => Kleisli.J (m := Trace)
local notation "M" => Kleisli.types

noncomputable local instance : InstructionModel J M signature.Instr := Kleisli.instructions model
local instance : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent

private noncomputable abbrev runAt {Γ : VCtx (Ty Empty)} {r : Region signature.Instr}
    (h : ValueBranches Γ r Exits) (x : ctxObj M Γ) : Trace (value (packedExitType Exits)) :=
  (denoteRegion J M h.hasType ≫ (J).map (packLabel M Exits)).of x

set_option backward.isDefEq.respectTransparency false in
private theorem case_run {Γ : VCtx (Ty Empty)} {A B : Ty Empty} {a : Tm signature.Instr}
    {l r : Region signature.Instr} {ha : Tm.HasType Γ a (coprod A B)}
    {sa : (J).obj (ctxObj M Γ) ⟶ (J).obj (value (coprod A B))}
    (d : Denotes J M ha sa) (hl : ValueBranches (A :: Γ) l Exits)
    (hr : ValueBranches (B :: Γ) r Exits) (x : ctxObj M Γ) :
    runAt (.case ha hl hr) x =
      Bind.bind (m := Trace) (sa.of x)
        (fun | .inl a => runAt hl (x, a) | .inr b => runAt hr (x, b)) := by
  have h := RegionDenotes.eq_denote J M
    (.case d (denoteRegion_spec J M hl.hasType) (denoteRegion_spec J M hr.hasType))
  unfold runAt
  erw [← h, case_postcomp J, caseWithContext_of (m := Trace)]
  simp only [Kleisli.Type.comp_of_eq_kleisliRight, Bind.kleisliRight]
  have coord (v : value (coprod A B)) :
      (Types.binaryCoproductIso ((M).obj A) ((M).obj B)).hom (((M).coprodIso A B).hom v) = v :=
    ConcreteCategory.congr_hom (Types.binaryCoproductIso (value A) (value B)).inv_hom_id v
  change Bind.bind (m := Trace) (Bind.bind (m := Trace) (sa.of x)
    (fun v => pure (((M).coprodIso A B).hom v))) _ = _
  simp only [bind_assoc, pure_bind, coord]
  congr 1
  funext reply
  cases reply <;> rfl

private theorem test_run {Γ : VCtx (Ty Empty)} {l r : Region signature.Instr}
    (hl : ValueBranches (U :: Bit :: Γ) l Exits) (hr : ValueBranches (U :: Bit :: Γ) r Exits)
    (x : ctxObj M Γ) (b : Bool) :
    runAt (.case (.var (i := 0) rfl) hl hr) (x, bit b) =
      if b then runAt hr ((x, bit b), PUnit.unit) else runAt hl ((x, bit b), PUnit.unit) := by
  have h := case_run (Denotes.var («J» := Kleisli.J (m := Trace)) («M» := Kleisli.types) (i := 0) rfl)
    hl hr (x, bit b)
  change runAt (.case (.var (i := 0) rfl) hl hr) (x, bit b) =
    Bind.bind (m := Trace) (pure (bit b)) _ at h
  erw [h, pure_bind]
  cases b <;> rfl

private noncomputable abbrev queryConst (Γ : VCtx (Ty Empty)) (b : Bool) :
    ctxObj M Γ ⟶ value Bit := TypeCat.ofHom (fun _ => bit b)

set_option backward.isDefEq.respectTransparency false in
private theorem literal_denotes (Γ : VCtx (Ty Empty)) (b : Bool) :
    Denotes J M ((constructorBit_value (Γ := Γ) b .unit).hasType) ((J).map (queryConst Γ b)) := by
  cases b
  · have eq : queryConst Γ false =
        (SemiCartesianMonoidalCategory.toUnit (ctxObj M Γ) ≫ (M).unitIso.inv) ≫
          coprod.inl ≫ ((M).coprodIso U U).inv := by
      have coordinate := Types.binaryCoproductIso_inl_comp_hom (value U) (value U)
      change queryConst Γ false = (_ ≫ coprod.inl ≫
        (Types.binaryCoproductIso (value U) (value U)).hom)
      rw [coordinate]
      rfl
    rw [eq, (J).map_comp]
    exact .inl .unit
  · have eq : queryConst Γ true =
        (SemiCartesianMonoidalCategory.toUnit (ctxObj M Γ) ≫ (M).unitIso.inv) ≫
          coprod.inr ≫ ((M).coprodIso U U).inv := by
      have coordinate := Types.binaryCoproductIso_inr_comp_hom (value U) (value U)
      change queryConst Γ true = (_ ≫ coprod.inr ≫
        (Types.binaryCoproductIso (value U) (value U)).hom)
      rw [coordinate]
      rfl
    rw [eq, (J).map_comp]
    exact .inr .unit

set_option backward.isDefEq.respectTransparency false in
private theorem request_case_run {Γ : VCtx (Ty Empty)} {l r : Region signature.Instr}
    (label b : Bool) (hl : ValueBranches (Bit :: Γ) l Exits) (hr : ValueBranches (Bit :: Γ) r Exits)
    (x : ctxObj M Γ) :
    runAt (.case (.op (f := (show signature.Instr from .ask label))
      (constructorBit_value b .unit).hasType) hl hr) x =
      (request label (bit b) >>= fun | .inl a => runAt hl (x, a) | .inr a => runAt hr (x, a)) := by
  let op : signature.Instr := .ask label
  have d : Denotes J M (.op (f := op) (constructorBit_value b .unit).hasType)
      ((J).map (queryConst Γ b) ≫ (Kleisli.instructions model).denote op) :=
    .op (literal_denotes Γ b)
  rw [case_run d hl hr x]
  erw [Kleisli.Type.comp_of_eq_kleisliRight]
  change Bind.bind (m := Trace) (Bind.bind (m := Trace) (pure (bit b)) (request label)) _ = _
  rw [pure_bind]
  congr 1
  funext reply
  cases reply <;> rfl

set_option backward.isDefEq.respectTransparency false in
private theorem branch_run {Γ : VCtx (Ty Empty)} (x : ctxObj M Γ) (v : value Bit)
    (i : Nat) (hi : At Exits i Bit) :
    runAt (Γ := Bit :: Γ) (.br hi (.var (i := 0) rfl)) (x, v) = pure ((packedLabelInject M i hi) v) := by
  unfold runAt
  have d := RegionDenotes.eq_denote J M
    (RegionDenotes.br (h := hi) (Denotes.var («J» := Kleisli.J (m := Trace)) («M» := Kleisli.types)
      (Φ := signature.Instr) (i := 0) (rfl : At (Bit :: Γ) 0 Bit)))
  erw [← d]
  have comp := (J).map_comp (labelInject M i hi) (packLabel M Exits)
  erw [Category.assoc, ← comp, labelInject_packLabel, Kleisli.Type.comp_of_eq_kleisliRight]
  change Bind.bind (m := Trace) (pure v) (fun y => pure ((packedLabelInject M i hi) y)) = _
  rw [pure_bind]

set_option backward.isDefEq.respectTransparency false in
private theorem call_run {Γ : VCtx (Ty Empty)} (label b : Bool) (x : ctxObj M Γ) :
    runAt (call_typed label (constructorBit_value b .unit).hasType) x =
      (request label (bit b) >>= fun reply => pure (atExit reply)) := by
  let left : ValueBranches (Φ := signature.Instr) (Bit :: Γ) (.br 0 (.var 0)) Exits := .br rfl (.var (i := 0) rfl)
  let right : ValueBranches (Φ := signature.Instr) (Bit :: Γ) (.br 1 (.var 0)) Exits := .br rfl (.var (i := 0) rfl)
  refine (request_case_run label b left right x).trans ?_
  congr 1
  funext reply
  cases reply with
  | inl v =>
    change runAt left (x, v) = pure (atExit (.inl v))
    erw [branch_run x v 0 (rfl : At Exits 0 Bit)]
    congr 1
    simp only [packedLabelInject, eqToHom_refl, Category.id_comp]
    exact ConcreteCategory.congr_hom (Types.binaryCoproductIso_inl_comp_hom
      (value Bit) (value (packedExitType [Bit]))) v
  | inr v =>
    change runAt right (x, v) = pure (atExit (.inr v))
    erw [branch_run x v 1 (rfl : At Exits 1 Bit)]
    congr 1
    simp only [packedLabelInject, eqToHom_refl, Category.id_comp, Category.assoc]
    have inner := ConcreteCategory.congr_hom
      (Types.binaryCoproductIso_inl_comp_hom (value Bit) (value (packedExitType []))) v
    have outer := ConcreteCategory.congr_hom
      (Types.binaryCoproductIso_inr_comp_hom (value Bit) (value (packedExitType [Bit])))
        (Sum.inl v : value (packedExitType [Bit]))
    change (coprod.inr ≫ (Types.binaryCoproductIso (value Bit) (value (packedExitType [Bit]))).hom)
      ((coprod.inl ≫ (Types.binaryCoproductIso (value Bit) (value (packedExitType []))).hom) v) = _
    rw [inner]
    exact outer

private def replyBit : value Answer → Bool
  | .inl a | .inr a => queryBit a

private theorem row_run (k : Key) (g : Bool) (x : ctxObj M [U, Bit]) (a : value Bit) :
    runAt (compile_typed k.secondLabel (k.row g) (Γ := [Bit, U, Bit]) (slots := replySlot) (fun _ => .var (i := 0) rfl))
        (x, a) =
      (request k.secondLabel (bit (k.secondQuery (assignment g (queryBit a)))) >>=
        fun r => pure (atExit r)) := by
  have execute (b : Bool) : runAt
      (compile_typed k.secondLabel (k.row g) (Γ := [Bit, U, Bit]) (slots := replySlot) (fun _ => .var (i := 0) rfl))
      (x, bit b) =
      (request k.secondLabel (bit (k.secondQuery (assignment g (queryBit (bit b))))) >>=
        fun r => pure (atExit r)) := by
    let next (r : Bool) := call_typed k.secondLabel (Γ := [U, Bit, U, Bit])
      (constructorBit_value (k.secondQuery (assignment g r)) .unit).hasType
    refine (test_run (next false) (next true) x b).trans ?_
    cases b <;> exact call_run _ _ _
  cases a with
  | inl u => cases u; exact execute false
  | inr u => cases u; exact execute true

private theorem key_run (k : Key) (g : Bool) :
    (denote.map k.packed).of (bit g) =
      (request k.firstLabel (bit g) >>= fun firstReply =>
        request k.secondLabel (bit (k.secondQuery (assignment g (replyBit firstReply)))) >>= fun secondReply =>
          pure (atExit secondReply)) := by
  let sound : Paper.Extension.Singleton.SeedDenotes (Seed := Seed) J M :=
    Paper.WithCaseBind.joined_seedDenotes J M
      (Paper.WithPairReturns.joined_seedDenotes J M (fun _ _ => ⟨rfl, rfl⟩) false)
  change ((Paper.Extension.Singleton.denoteFunctor J M (fun _ _ => ⟨rfl, rfl⟩) sound).map
    (Paper.Extension.Singleton.ofRegion Seed k.typed.packExits)).of (bit g) = _
  rw [Paper.Extension.Singleton.denoteFunctor_map_ofRegion]
  unfold denoteSingletonRegion
  change (((J).map _ ≫ denoteRegion J M k.typed.hasType.packExits ≫ (J).map _)).of (bit g) = _
  rw [denoteRegion_packExits_valueBranches J M (fun _ _ => ⟨rfl, rfl⟩) k.typed]
  have combine : packLabelExit M Exits ≫ singletonLabelPayload M (packedExitType Exits) = packLabel M Exits := by
    unfold packLabelExit
    rw [Category.assoc, SingletonDispatcher.labelInject_payload, Category.comp_id]
  simp only [Category.assoc, ← (J).map_comp, combine]
  erw [Kleisli.Type.comp_of_eq_kleisliRight]
  change Bind.bind (m := Trace) (pure (PUnit.unit, bit g))
    (fun x => runAt k.typed x) = _
  rw [pure_bind]
  have execute (b : Bool) :
      runAt (first_typed k.firstLabel b
        (compile_typed k.secondLabel (k.row b) (Γ := [Bit, U, Bit]) (slots := replySlot) (fun _ => .var (i := 0) rfl)))
        ((PUnit.unit, bit b), PUnit.unit) =
      (request k.firstLabel (bit b) >>= fun firstReply =>
        request k.secondLabel (bit (k.secondQuery (assignment b (replyBit firstReply)))) >>= fun secondReply =>
          pure (atExit secondReply)) := by
    let next := compile_typed k.secondLabel (k.row b) (Γ := [Bit, U, Bit]) (slots := replySlot)
      (fun _ => .var (i := 0) rfl)
    refine (request_case_run k.firstLabel b next next ((PUnit.unit, bit b), PUnit.unit)).trans ?_
    congr 1
    funext a
    cases a
    all_goals exact row_run k b _ _
  let arm (b : Bool) := first_typed k.firstLabel b
    (compile_typed k.secondLabel (k.row b) (Γ := [Bit, U, Bit]) (slots := replySlot)
      (fun _ => .var (i := 0) rfl))
  refine (test_run (Γ := []) (arm false) (arm true) PUnit.unit g).trans ?_
  cases g <;> exact execute _

private theorem queryBit_bit (b : Bool) : queryBit (bit b) = b := by cases b <;> rfl

private theorem replyBit_answer (reply : Reply) : replyBit (answer reply.1 reply.2) = reply.2 := by
  obtain ⟨right, b⟩ := reply
  cases right <;> cases b <;> rfl

private theorem bind_request {A : Type} (label b : Bool) (next : value Answer → Trace A)
    (result : Except Bool A) (word : FreeMonoid Event) :
    (result, word) ∈ (request label (bit b) >>= next).outcomes ↔
      ∃ (reply : Reply) (tail : FreeMonoid Event), (result, tail) ∈ (next (answer reply.1 reply.2)).outcomes ∧
        FreeMonoid.of ⟨label, b, reply.1, reply.2⟩ * tail = word := by
  rw [Tagged.mem_bind]
  simp only [request, Tagged.outcomes_ofOutcomes, queryBit_bit]
  constructor
  · rintro (⟨fault, _, ⟨reply, bad⟩⟩ | ⟨a, u, v, ⟨reply, h⟩, hv, hw⟩)
    · cases (congrArg Prod.fst bad : Except.ok (answer reply.1 reply.2) = Except.error fault)
    · rcases Prod.mk.inj h with ⟨ha, hu⟩
      exact ⟨reply, v, Except.ok.inj ha ▸ hv, hu.symm ▸ hw⟩
  · rintro ⟨reply, v, hv, hw⟩
    exact Or.inr ⟨answer reply.1 reply.2, _, v, ⟨reply, rfl⟩, hv, hw⟩

private theorem key_outcomes (k : Key) (g : Bool) : k.observations g = k.outcomes g := by
  unfold Key.observations
  refine (congrArg (Tagged.outcomes (A := value (packedExitType Exits))) (key_run k g)).trans ?_
  apply Set.ext
  rintro ⟨result, word⟩
  rw [bind_request]
  constructor
  · rintro ⟨firstReply, tail, h, wordEq⟩
    simp only [replyBit_answer] at h
    rw [bind_request] at h
    obtain ⟨secondReply, done, hp, tailEq⟩ := h
    have hp' : (result, done) = (.ok (atExit (answer secondReply.1 secondReply.2)), 1) := hp
    rcases Prod.mk.inj hp' with ⟨resultEq, doneEq⟩
    refine ⟨(firstReply, secondReply), Prod.ext resultEq.symm ?_⟩
    change k.word g firstReply secondReply = word
    rw [Key.word, ← wordEq, ← tailEq, doneEq, mul_one]
  · rintro ⟨⟨firstReply, secondReply⟩, h⟩
    cases h
    refine ⟨firstReply, FreeMonoid.of ⟨k.secondLabel, k.secondQuery (assignment g firstReply.2),
      secondReply.1, secondReply.2⟩, ?_, rfl⟩
    simp only [replyBit_answer]
    rw [bind_request]
    exact ⟨secondReply, 1, rfl, mul_one _⟩

theorem packed_outcomes (p : Program) (g : Bool) : p.observations g = p.key.outcomes g := by
  unfold Program.observations
  rw [packed_replay]
  exact key_outcomes p.key g

private theorem log_events {k l : Key} {g : Bool} {r₁ r₂ s₁ s₂ : Reply}
    (h : k.word g r₁ r₂ = l.word g s₁ s₂) :
    (⟨k.firstLabel, g, r₁.1, r₁.2⟩ : Event) = ⟨l.firstLabel, g, s₁.1, s₁.2⟩ ∧
    (⟨k.secondLabel, k.secondQuery (assignment g r₁.2), r₂.1, r₂.2⟩ : Event) =
      ⟨l.secondLabel, l.secondQuery (assignment g s₁.2), s₂.1, s₂.2⟩ := by
  have words := congrArg FreeMonoid.toList h
  exact ⟨(List.cons.inj words).1, List.singleton_inj.mp (List.cons.inj words).2⟩

private theorem recover_key {k l : Key} (same : ∀ g, k.outcomes g = l.outcomes g) : k = l := by
  have detect (g r : Bool) :
      k.firstLabel = l.firstLabel ∧ k.secondLabel = l.secondLabel ∧
      k.secondQuery (assignment g r) = l.secondQuery (assignment g r) := by
    have hit : (.ok (atExit (answer false false)), k.word g (false, r) (false, false)) ∈ l.outcomes g :=
      (same g) ▸ (show _ ∈ k.outcomes g from ⟨((false, r), (false, false)), rfl⟩)
    rcases hit with ⟨⟨r₁, r₂⟩, sameLog⟩
    obtain ⟨firstEq, secondEq⟩ := log_events (congrArg Prod.snd sameLog).symm
    have eq : r = r₁.2 := congrArg Event.payload firstEq
    exact ⟨congrArg Event.label firstEq, congrArg Event.label secondEq,
      (congrArg Event.query secondEq).trans (congrArg (fun b => l.secondQuery (assignment g b)) eq.symm)⟩
  have exhaustive (env : Assignment 2) : assignment (env 1) (env 0) = env := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    rw [Fin.eq_zero j]
    rfl
  have tables : k.secondQuery = l.secondQuery := funext fun env =>
    exhaustive env ▸ (detect (env 1) (env 0)).2.2
  have firstLabel := (detect false false).1
  have secondLabel := (detect false false).2.1
  cases k
  cases l
  simp only [Key.mk.injEq]
  exact ⟨firstLabel, secondLabel, tables⟩

theorem packed_eq_iff_key (p q : Program) : p.packed = q.packed ↔ p.key = q.key := by
  constructor
  · intro eq
    apply recover_key
    intro g
    rw [← packed_outcomes, ← packed_outcomes]
    unfold Program.observations
    rw [eq]
  · intro eq
    exact (packed_replay p).trans ((congrArg Key.packed eq).trans (packed_replay q).symm)

theorem observations_iff_packed_eq (p q : Program) :
    (∀ g, p.observations g = q.observations g) ↔ p.packed = q.packed := by
  constructor
  · intro same
    apply (packed_eq_iff_key p q).2
    exact recover_key (fun g => (packed_outcomes p g).symm.trans ((same g).trans (packed_outcomes q g)))
  · intro eq g
    unfold Program.observations
    rw [eq]

theorem xor_quote_replay : Example.xor.packed = Example.xorQuote.packed := by
  apply (packed_eq_iff_key _ _).2
  have rows : Example.xor.key.secondQuery = Example.xorQuote.key.secondQuery :=
    (funext (Expr.quote_eval 2 Example.xor.key.secondQuery)).symm
  exact congrArg (Key.mk true false) rows

theorem second_query_witness :
    Example.observation true ∈ Example.xor.observations true ∧
    Example.observation false ∈ Example.replyOnly.observations true ∧
    Example.observation true ∉ Example.replyOnly.observations true := by
  rw [packed_outcomes, packed_outcomes]
  refine ⟨⟨((true, false), (true, false)), rfl⟩, ⟨((true, false), (true, false)), rfl⟩, ?_⟩
  rintro ⟨⟨r, s⟩, h⟩
  have word : Example.replyOnly.key.word true r s =
      Example.xor.key.word true (true, false) (true, false) := congrArg Prod.snd h
  obtain ⟨first, second⟩ := log_events word
  have payload : r.2 = false := congrArg Event.payload first
  have query : r.2 = true := congrArg Event.query second
  exact Bool.false_ne_true (payload.symm.trans query)

theorem second_query_ne : Example.xor.packed ≠ Example.replyOnly.packed := by
  intro eq
  have same := (observations_iff_packed_eq _ _).2 eq true
  exact second_query_witness.2.2 (same ▸ second_query_witness.1)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TwoBitQueries
