module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Packed.ReplyAgreement.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Packed.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.Selected.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Case.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Kleisli.Thms

/-! # The selected fold at the witnessed payload separator's coordinates -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedCaseReplyAgreement

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open CategoryTheory CategoryTheory.Limits
open Semantics.Categorical
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext caseWithContext_of pair_of)
open Silmaril.Isotope.LetIter.Semantics.Categorical (case_postcomp)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply (Trace Log Outcome Event prepend)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
  (Bit Answer Position signature Op model modelCoherent)
open Silmaril.Semantics.NondeterministicTrace (Tagged)

local notation "J" => Kleisli.J (m := Trace)
local notation "M" => Kleisli.types
local notation "PJ" => Paper.WithProjectionReturnsAndUnitEta.denoteArrow
local notation "pack" => Paper.WithProjectionReturnsAndUnitEta.ExitPacking.packArrow

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

noncomputable local instance : Silmaril.Isotope.LetIter.Semantics.Categorical.InstructionModel J M signature.Instr :=
  Kleisli.instructions model

local instance : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent

set_option backward.isDefEq.respectTransparency false

private abbrev emit (b : Bool) : Trace PUnit :=
  Tagged.ofOutcomes {(.ok PUnit.unit, FreeMonoid.of (Event.emit b))}

private abbrev ask (request : Bool) : Trace (value Answer) :=
  Tagged.ofOutcomes (Set.range fun reply : Bool × Bool =>
    (.ok (Reply.Payload.answer reply.1 reply.2), Reply.Payload.replyLog request reply.1 reply.2))

private theorem packed_injection {L : List (Ty Empty)} (i : Nat) {A : Ty Empty}
    (hi : At L i A) (x : value A) :
    (labelInject M i hi ≫ packLabel M L) x = Reply.Exits.packAt L i hi x := by
  have coordinate := ConcreteCategory.congr_hom (labelInject_packLabel M hi) x
  refine coordinate.trans ?_
  clear coordinate
  induction L generalizing i with
  | nil => cases i <;> contradiction
  | cons B L ih =>
    cases i with
    | zero =>
      cases Option.some.inj hi
      simp only [packedLabelInject, Reply.Exits.packAt, eqToHom_refl, Category.id_comp]
      exact ConcreteCategory.congr_hom
        (Types.binaryCoproductIso_inl_comp_hom (value A) (value (packedExitType L))) x
    | succ i =>
      simp only [packedLabelInject, Reply.Exits.packAt]
      change (coprod.inr ≫ (Types.binaryCoproductIso (value B) (value (packedExitType L))).hom)
        (packedLabelInject M i hi x) = _
      rw [Types.binaryCoproductIso_inr_comp_hom, ih i hi]
      rfl

private theorem packed_position {L : List (Ty Empty)} (pos : Position L) (b : Bool) :
    (labelInject M pos.1 pos.typed ≫ packLabel M L) (Reply.Payload.bit b) =
      (pos.result b).packed := by
  rw [packed_injection]
  have castPack {A B : Ty Empty} (e : A = B) {i : Nat} (h : At L i A) (v : value B) :
      Reply.Exits.packAt L i (e ▸ h) v = Reply.Exits.packAt L i h (e.symm ▸ v) := by
    cases e
    rfl
  exact castPack pos.2 (labelAt_get L pos.1) (Reply.Payload.bit b)

private theorem emitPrefix_of {X : Ty Empty} (bits : List Bool) (body : Term signature.Instr X Bit)
    (x : value X) :
    ((emitPrefix bits body).targetArrow J M).of x =
      bits.foldr (fun b next => emit b >>= fun _ => next) ((body.targetArrow J M).of x) := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    simp only [emitPrefix, Term.targetArrow, orderedPair_eq_pair, Category.assoc,
      Kleisli.Type.comp_of_eq_kleisliRight, Bind.kleisliRight]
    rw [pair_of (m := Trace)]
    simp only [Kleisli.Type.comp_of_eq_kleisliRight, Bind.kleisliRight]
    change Bind.bind (m := Trace) (Bind.bind (m := Trace)
        (Bind.bind (m := Trace) (pure PUnit.unit) (fun _ => emit b))
        (fun u => Bind.bind (m := Trace) (((emitPrefix bs body).targetArrow J M).of x)
          (fun z => pure (u, z))))
      (fun p => Bind.bind (m := Trace) (pure p) (fun z => pure z.2)) = _
    simp only [pure_bind, bind_assoc, bind_pure, List.foldr, ih]

private theorem payloadLeaf_of {L : List (Ty Empty)} (bits : List Bool) (pos : Position L)
    (b : Bool) :
    (((J).map ((M).productIso unit Bit).inv ≫ (payloadLeaf bits pos).targetArrow J M) ≫
      (J).map (packLabel M L)).of (PUnit.unit, Reply.Payload.bit b) =
      bits.foldr (fun bit next => emit bit >>= fun _ => next) (pure ((pos.result b).packed)) := by
  simp only [payloadLeaf, CaseTree.targetArrow, Program.targetArrow, Category.assoc,
    ← (J).map_comp, Kleisli.Type.comp_of_eq_kleisliRight, Bind.kleisliRight]
  change Bind.bind (m := Trace) (pure (PUnit.unit, Reply.Payload.bit b))
    (fun z => Bind.bind (m := Trace) (((emitPrefix bits (.snd unit Bit)).targetArrow J M).of z)
      (fun v => pure ((labelInject M pos.1 pos.typed ≫ packLabel M L) v))) = _
  rw [pure_bind, emitPrefix_of]
  induction bits with
  | nil =>
    change Bind.bind (m := Trace) (pure (Reply.Payload.bit b)) _ = _
    simp only [pure_bind, List.foldr, packed_position]
  | cons bit rest ih =>
    simp only [List.foldr, bind_assoc, ih]

private theorem query_of (request : Bool) :
    ((Term.call (X := unit) (show signature.Instr from Op.ask request) .unit).targetArrow J M ≫
      (J).map ((M).coprodIso Bit Bit).hom).of PUnit.unit =
      (ask request >>= fun s => pure (((M).coprodIso Bit Bit).hom s)) := by
  simp only [Term.targetArrow, Category.assoc, Kleisli.Type.comp_of_eq_kleisliRight, Bind.kleisliRight]
  change Bind.bind (m := Trace) (pure PUnit.unit)
    (fun _ => Bind.bind (m := Trace) (ask request) (fun s => pure (((M).coprodIso Bit Bit).hom s))) = _
  rw [pure_bind]

private theorem selected_of {L : List (Ty Empty)} (p : DirectProgram L) :
    (PJ J M (fun _ _ => ⟨rfl, rfl⟩) (pack p.selected.elaborate.property)).of PUnit.unit =
      (ask p.val.request >>= fun
        | .inl a => (((J).map ((M).productIso unit Bit).inv ≫
            (payloadLeaf p.val.left.emits p.val.left.position).targetArrow J M) ≫
              (J).map (packLabel M L)).of (PUnit.unit, a)
        | .inr b => (((J).map ((M).productIso unit Bit).inv ≫
            (payloadLeaf p.val.right.emits p.val.right.position).targetArrow J M) ≫
              (J).map (packLabel M L)).of (PUnit.unit, b)) := by
  rw [p.selected.denote_packArrow J M (fun _ _ => ⟨rfl, rfl⟩)]
  simp only [DirectProgram.selected, CaseTree.targetArrow]
  rw [case_postcomp J, caseWithContext_of (m := Trace)]
  simp only [Bind.kleisliRight]
  erw [query_of]
  have coordinate (s : value Answer) :
      (Types.binaryCoproductIso ((M).obj Bit) ((M).obj Bit)).hom (((M).coprodIso Bit Bit).hom s) = s :=
    ConcreteCategory.congr_hom (Types.binaryCoproductIso (value Bit) (value Bit)).inv_hom_id s
  simp only [bind_assoc, pure_bind, coordinate]
  congr 1
  funext reply
  cases reply <;> rfl

private theorem observe_bind {S A B : Type} (answer : S → A) (log : S → Log) (k : A → Trace B) :
    ((Tagged.ofOutcomes (Set.range fun s => (.ok (answer s), log s)) : Trace A) >>= k).outcomes =
      ⋃ s, (fun z : Outcome B => (z.1, log s * z.2)) '' (k (answer s)).outcomes := by
  ext z
  obtain ⟨result, word⟩ := z
  rw [Tagged.mem_bind, Set.mem_iUnion]
  constructor
  · rintro (⟨fault, _, ⟨s, hs⟩⟩ | ⟨a, u, v, ⟨s, hs⟩, hk, hw⟩)
    · cases (congrArg Prod.fst hs : Except.ok (answer s) = Except.error fault)
    · cases (Except.ok.inj (congrArg Prod.fst hs))
      cases (congrArg Prod.snd hs)
      exact ⟨s, (result, v), hk, congrArg (fun w => (result, w)) hw⟩
  · rintro ⟨s, ⟨⟨r, v⟩, hk, eq⟩⟩
    cases eq
    exact Or.inr ⟨answer s, log s, v, ⟨s, rfl⟩, hk, rfl⟩

private theorem emit_outcomes {A : Type} (bit : Bool) (next : Trace A) :
    (emit bit >>= fun _ => next).outcomes = prepend (.emit bit) '' next.outcomes := by
  simpa only [Set.range_const, Set.iUnion_const, prepend] using
    observe_bind (fun _ : Unit => (PUnit.unit : PUnit)) (fun _ => FreeMonoid.of (Event.emit bit)) (fun _ => next)

private theorem prefix_outcomes {D R : Type} (bits : List Bool) (success : R → D) (r : R) :
    (bits.foldr (fun b next => emit b >>= fun _ => next) (pure (success r))).outcomes =
      (bits.foldr Reply.Normal.emit (.ret r)).outcomesWith success := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.foldr, Reply.Normal.outcomesWith, emit_outcomes, ih]

private theorem leaf_observe {L : List (Ty Empty)} (a : Reply.Payload.Arm L)
    (direct : a.result = .payload) (b : Bool) :
    ((((J).map ((M).productIso unit Bit).inv ≫ (payloadLeaf a.emits a.position).targetArrow J M) ≫
        (J).map (packLabel M L)).of (PUnit.unit, Reply.Payload.bit b)).outcomes =
      (a.normal.traceTree b).outcomesWith Reply.Exits.Exit.packed := by
  rw [payloadLeaf_of, prefix_outcomes a.emits Reply.Exits.Exit.packed (a.position.result b)]
  cases b <;> simp only [Reply.Payload.ArmNormal.traceTree, Reply.Payload.ArmNormal.result,
    Reply.Payload.Arm.normal, direct, Reply.Payload.Expr.evaluate, Bool.false_eq_true, ↓reduceIte]

private theorem boolPair_union {A : Type} (f : Bool × Bool → Set A) :
    (⋃ r, f r) = (f (false, false) ∪ f (false, true)) ∪ (f (true, false) ∪ f (true, true)) := by
  rw [Set.iUnion_prod']
  change (⨆ i, ⨆ j, f (i, j)) = (f (false, false) ⊔ f (false, true)) ⊔ (f (true, false) ⊔ f (true, true))
  simp only [iSup_bool_eq, sup_comm]

/-- Both interpretations observe the same witnessed request, emit prefixes
and packed typed exits. The LetCase side uses its published evaluation. -/
theorem packed_outcomes (H : Ty Empty) (L : List (Ty Empty)) (p : DirectProgram (H :: L)) :
    ((PJ J M (fun _ _ => ⟨rfl, rfl⟩) (pack p.selected.elaborate.property)).of PUnit.unit).outcomes =
      Reply.Payload.programOutcomes H L p.val := by
  rw [selected_of, Reply.Payload.programOutcomes_eq, observe_bind, boolPair_union]
  simp only [Reply.Payload.answer, Bool.false_eq_true, ↓reduceIte,
    leaf_observe _ p.property.1, leaf_observe _ p.property.2, Reply.Payload.Normal.outcomes,
    Reply.Payload.Normal.traceTree, Reply.Payload.requestTree, Reply.Payload.ProgramBody.normal,
    Reply.Normal.outcomesWith, Set.image_union, Set.image_image, prepend, Reply.Payload.replyLog, mul_assoc]
  rfl

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedCaseReplyAgreement
