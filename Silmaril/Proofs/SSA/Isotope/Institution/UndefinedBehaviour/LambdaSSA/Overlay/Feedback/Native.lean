module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Graph

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Feedback
open Silmaril.Isotope.Institution.Observational
open Silmaril.Isotope.Morphism.SSAIter (envOfBound envOfBound_agrees)

universe u v w x

variable {Φ : Type u} {τ : Type v} [TypeFormers τ] [HasTy Φ τ] {Γ R L : List τ}
  (entry : UB.Typed (Φ := Φ) Γ (R ++ L))
  (blocks : (i : Fin R.length) → UB.Typed (Φ := Φ) (R.get i :: Γ) (R ++ L))

theorem nativeFeedback_hasType : (nativeFeedback entry blocks).HasType Γ L := by
  refine LambdaSSA.Region.HasType.cfg (List.get R) ?_ ?_
  · simpa only [List.ofFn_get] using entry.property
  · intro i
    simpa only [List.ofFn_get] using (blocks i).property

variable (M : Model.{u,w,x} Φ Γ.length)

local notation "captured" => envOfBound M.bound
private abbrev blockSyntax : Fin R.length → LambdaSSA.Region Φ := fun i => (blocks i).val

private noncomputable abbrev nativeGraph : Run R L M.α M.σ :=
  feedbackRun (.native entry) (fun i => .native (blocks i)) M

local notation "rawBlocks" => blockSyntax blocks
local notation "graph" => nativeGraph entry blocks M

private def pointState : Point R.length M.α M.σ → M.σ
  | .entry s | .block _ _ s => s

private def pointEnv : Point R.length M.α M.σ → Env M.α
  | .entry _ => captured
  | .block _ a _ => extend captured a

private def pointRegion : Point R.length M.α M.σ → LambdaSSA.Region Φ
  | .entry _ => entry.val
  | .block i _ _ => (blocks i).val

private abbrev LocalEval (p : Point R.length M.α M.σ) (label : Nat) (a : Value M.α) (s : M.σ) :=
  Semantics.Region.Eval M.instr (pointEnv M p) (pointRegion entry blocks M p) (pointState M p) label a s

private abbrev LocalFault (p : Point R.length M.α M.σ) (s : M.σ) :=
  Semantics.Region.Fault M.instr M.faults (pointEnv M p) (pointRegion entry blocks M p) (pointState M p) s

private abbrev LocalDiverges (p : Point R.length M.α M.σ) :=
  External.Diverges M.instr M.prim (.region (pointEnv M p) (pointRegion entry blocks M p) (pointState M p))

private theorem ordinary_coe {n : Nat} {α : Type w} {σ : Type x}
    (outcomes : Set (Outcome n α σ)) (o : Outcome n α σ) :
    Behaviour.Ordinary (WithTop.some outcomes) o ↔ o ∈ outcomes :=
  ⟨fun h => h.2, fun h => ⟨WithTop.coe_ne_top, h⟩⟩

private theorem nativeOrdinary (p : Point R.length M.α M.σ) (o : Outcome (R ++ L).length M.α M.σ) :
    (graph p).Ordinary o ↔
      match o with
      | .ret i a s => LocalEval entry blocks M p i a s
      | .fault s => LocalFault entry blocks M p s
      | .diverge => LocalDiverges entry blocks M p := by
  cases p with
  | entry s =>
    cases o <;> exact (ordinary_coe (nativeOutcomes entry M s) _).trans
      (mem_nativeOutcomes_iff entry (M := M) (envOfBound_agrees M.bound) s _)
  | block i a s =>
    cases o <;> exact (ordinary_coe (nativeOutcomes (blocks i) (extendModel M a) s) _).trans
      (mem_nativeOutcomes_iff (blocks i) (M := extendModel M a)
        ((envOfBound_agrees M.bound).extend a) s _)

private theorem step_of_eval {p : Point R.length M.α M.σ}
    {i : Fin R.length} {a : Value M.α} {s : M.σ}
    (h : LocalEval entry blocks M p i a s) :
    Step graph p (.block i a s) :=
  .branch ((nativeOrdinary entry blocks M p (.ret (internal R L i) a s)).mpr h)

private def Returns (p : Point R.length M.α M.σ) (label : Nat) (a : Value M.α) (s' : M.σ) : Prop :=
  match p with
  | .entry s => Semantics.Region.Eval M.instr captured (nativeFeedback entry blocks) s label a s'
  | .block i value s => Semantics.Region.Follow M.instr captured rawBlocks i.val value s label a s'

private def Faults (p : Point R.length M.α M.σ) (s' : M.σ) : Prop :=
  match p with
  | .entry s => Semantics.Region.Fault M.instr M.faults captured (nativeFeedback entry blocks) s s'
  | .block i a s => Semantics.Region.FollowFault M.instr M.faults captured rawBlocks i.val a s s'

private def nativeConfig : Point R.length M.α M.σ → Config M.α Φ M.σ
  | .entry s => .region captured (nativeFeedback entry blocks) s
  | .block i a s => .follow captured rawBlocks i.val a s

private theorem prepend_return {p : Point R.length M.α M.σ}
    {label out : Nat} {a value : Value M.α} {mid s' : M.σ}
    (head : LocalEval entry blocks M p label a mid)
    (tail : Semantics.Region.Follow M.instr captured rawBlocks label a mid out value s') :
    Returns entry blocks M p out value s' := by
  cases p with
  | entry s => exact Semantics.Region.Eval.cfg head tail
  | block i a s => exact Semantics.Region.Follow.step i.isLt head tail

private theorem prepend_fault {p : Point R.length M.α M.σ}
    {label : Nat} {a : Value M.α} {mid s' : M.σ}
    (head : LocalEval entry blocks M p label a mid)
    (tail : Semantics.Region.FollowFault M.instr M.faults captured rawBlocks label a mid s') :
    Faults entry blocks M p s' := by
  cases p with
  | entry s => exact Semantics.Region.Fault.cfg_follow head tail
  | block i a s => exact Semantics.Region.FollowFault.step i.isLt head tail

-- Keep the environment and block count general during induction on native paths.
private theorem follow_induct {α : Type w} {σ : Type x}
    {instr : Φ → Value α → σ → Value α → σ → Prop} {env : Env α} {n : Nat}
    {bs : Fin n → LambdaSSA.Region Φ} {first out : Nat} {a value : Value α} {mid s' : σ}
    (tail : Semantics.Region.Follow instr env bs first a mid out value s')
    {P : Nat → Value α → σ → Nat → Value α → σ → Prop}
    (exit : ∀ label a s, n ≤ label → P label a s (label - n) a s)
    (step : ∀ {label next out current middle value s mid s'} (inside : label < n),
      Semantics.Region.Eval instr (extend env current) (bs ⟨label, inside⟩) s next middle mid →
      P next middle mid out value s' → P label current s out value s') :
    P first a mid out value s' := by
  induction tail using Semantics.Region.Follow.rec (motive_1 := fun _ _ _ _ _ _ _ => True) with
  | exit outside => exact exit _ _ _ outside
  | step inside run _ _ ih => exact step inside run (ih exit step)
  | _ => trivial

private theorem followFault_induct {α : Type w} {σ : Type x}
    {instr : Φ → Value α → σ → Value α → σ → Prop}
    {faults : Φ → Value α → σ → σ → Prop} {env : Env α} {n : Nat}
    {bs : Fin n → LambdaSSA.Region Φ} {first : Nat} {a : Value α} {mid s' : σ}
    (tail : Semantics.Region.FollowFault instr faults env bs first a mid s')
    {P : Nat → Value α → σ → σ → Prop}
    (body : ∀ {label a s s'} (inside : label < n),
      Semantics.Region.Fault instr faults (extend env a) (bs ⟨label, inside⟩) s s' → P label a s s')
    (step : ∀ {label next a value s mid s'} (inside : label < n),
      Semantics.Region.Eval instr (extend env a) (bs ⟨label, inside⟩) s next value mid →
      P next value mid s' → P label a s s') :
    P first a mid s' := by
  induction tail using Semantics.Region.FollowFault.rec (motive_1 := fun _ _ _ _ _ => True) with
  | body inside fault _ => exact body inside fault
  | step inside head _ ih => exact step inside head (ih body step)
  | _ => trivial

private theorem return_path {first out : Nat} {a value : Value M.α} {mid s' : M.σ}
    (tail : Semantics.Region.Follow M.instr captured rawBlocks first a mid out value s') :
    ∀ (p : Point R.length M.α M.σ), LocalEval entry blocks M p first a mid →
      ∀ (j : Fin L.length), j.val = out → Finite graph p (.ret j value s') := by
  apply follow_induct tail (P := fun label a mid out value s' =>
    ∀ p, LocalEval entry blocks M p label a mid →
      ∀ (j : Fin L.length), j.val = out → Finite graph p (.ret j value s'))
  · intro first a mid outside p head j label
    refine ⟨p, .refl, (nativeOrdinary entry blocks M p (external R L (.ret j _ _))).mpr ?_⟩
    change LocalEval entry blocks M p (R.length + j.val) _ _
    convert head using 1
    omega
  · intro first next out current middle value before mid s' inside head ih p run j label
    obtain ⟨q, path, finish⟩ := ih (.block ⟨first, inside⟩ current before) head j label
    exact ⟨q, path.head (step_of_eval entry blocks M (i := ⟨first, inside⟩) run), finish⟩

private theorem finite_return_iff {p : Point R.length M.α M.σ} {j : Fin L.length}
    {value : Value M.α} {s' : M.σ} :
    Finite graph p (.ret j value s') ↔ Returns entry blocks M p j value s' := by
  constructor
  · rintro ⟨q, path, finish⟩
    induction path using Relation.ReflTransGen.head_induction_on with
    | refl =>
      have run := (nativeOrdinary entry blocks M q _).mp finish
      refine prepend_return entry blocks M run ?_
      simpa only [Nat.add_sub_cancel_left, Fin.val_cast, Fin.val_natAdd] using
        (Semantics.Region.Follow.exit (instr := M.instr) (env := captured) (blocks := rawBlocks)
          (value := value) (s := s') (Nat.le_add_right R.length j.val))
    | head edge _ ih =>
      cases edge with
      | branch run =>
        exact prepend_return entry blocks M ((nativeOrdinary entry blocks M _ _).mp run) ih
  · intro h
    cases p with
    | entry s =>
      change Semantics.Region.Eval M.instr captured (nativeFeedback entry blocks) s j value s' at h
      cases h with
      | cfg head tail => exact return_path entry blocks M tail (.entry s) head j rfl
    | block i a s =>
      change Semantics.Region.Follow M.instr captured rawBlocks i.val a s j.val value s' at h
      generalize labelEq : j.val = label at h
      cases h with
      | exit outside => exact (Nat.not_le_of_lt i.isLt outside).elim
      | step inside head tail =>
        exact return_path entry blocks M tail (.block i a s) head j labelEq

private theorem fault_path {first : Nat} {a : Value M.α} {mid s' : M.σ}
    (tail : Semantics.Region.FollowFault M.instr M.faults captured rawBlocks first a mid s') :
    ∀ (p : Point R.length M.α M.σ), LocalEval entry blocks M p first a mid →
      Finite graph p (.fault s') := by
  apply followFault_induct tail (P := fun label a mid s' =>
    ∀ p, LocalEval entry blocks M p label a mid → Finite graph p (.fault s'))
  · intro first a mid s' inside fault p head
    exact ⟨.block ⟨first, inside⟩ a mid, .single (step_of_eval entry blocks M head),
      (nativeOrdinary entry blocks M _ (.fault s')).mpr fault⟩
  · intro first next a value before mid s' inside head ih p run
    obtain ⟨q, path, finish⟩ := ih (.block ⟨first, inside⟩ a before) head
    exact ⟨q, path.head (step_of_eval entry blocks M (i := ⟨first, inside⟩) run), finish⟩

private theorem finite_fault_iff {p : Point R.length M.α M.σ} {s' : M.σ} :
    Finite graph p (.fault s') ↔ Faults entry blocks M p s' := by
  constructor
  · rintro ⟨q, path, finish⟩
    induction path using Relation.ReflTransGen.head_induction_on with
    | refl =>
      have fault := (nativeOrdinary entry blocks M q (.fault s')).mp finish
      cases q with
      | entry s => exact Semantics.Region.Fault.cfg_entry fault
      | block i a s => exact Semantics.Region.FollowFault.body i.isLt fault
    | head edge _ ih =>
      cases edge with
      | branch run =>
        exact prepend_fault entry blocks M ((nativeOrdinary entry blocks M _ _).mp run) ih
  · intro h
    cases p with
    | entry s =>
      change Semantics.Region.Fault M.instr M.faults captured (nativeFeedback entry blocks) s s' at h
      cases h with
      | cfg_entry fault =>
        exact ⟨.entry s, .refl, (nativeOrdinary entry blocks M _ (.fault s')).mpr fault⟩
      | cfg_follow head tail => exact fault_path entry blocks M tail (.entry s) head
    | block i a s =>
      change Semantics.Region.FollowFault M.instr M.faults captured rawBlocks i.val a s s' at h
      cases h with
      | body _ fault =>
        exact ⟨.block i a s, .refl, (nativeOrdinary entry blocks M _ (.fault s')).mpr fault⟩
      | step _ head tail => exact fault_path entry blocks M tail (.block i a s) head

private theorem step_config {p q : Point R.length M.α M.σ}
    {continues : Config M.α Φ M.σ → Prop} (edge : Step graph p q)
    (next : continues (nativeConfig entry blocks M q)) :
    External.DivergenceStep M.instr M.prim continues (nativeConfig entry blocks M p) := by
  cases edge with
  | branch run =>
    have head := (nativeOrdinary entry blocks M p _).mp run
    cases p with
    | entry s => exact .core (.cfg_follow head next)
    | block i a s => exact .core (.follow_next i.isLt head next)

private theorem diverges_after_eval {p : Point R.length M.α M.σ}
    {label : Nat} {a : Value M.α} {mid : M.σ}
    (head : LocalEval entry blocks M p label a mid)
    (tail : External.Diverges M.instr M.prim (.follow captured rawBlocks label a mid)) :
    ∃ q, Step graph p q ∧ External.Diverges M.instr M.prim (nativeConfig entry blocks M q) := by
  have inside : label < R.length := by
    cases tail.unfold with
    | core step => cases step <;> assumption
  exact ⟨.block ⟨label, inside⟩ a mid, step_of_eval entry blocks M head, tail⟩

private theorem diverges_unfold (p : Point R.length M.α M.σ)
    (h : External.Diverges M.instr M.prim (nativeConfig entry blocks M p)) :
    (graph p).Ordinary .diverge ∨
      ∃ q, Step graph p q ∧ External.Diverges M.instr M.prim (nativeConfig entry blocks M q) := by
  cases p with
  | entry s =>
    change External.Diverges M.instr M.prim (.region captured (.cfg entry.val R.length rawBlocks) s) at h
    cases h.unfold with
    | core step =>
      cases step with
      | cfg_entry localDiv => exact Or.inl ((nativeOrdinary entry blocks M _ .diverge).mpr localDiv)
      | cfg_follow head tail => exact Or.inr (diverges_after_eval entry blocks M head tail)
  | block i a s =>
    change External.Diverges M.instr M.prim (.follow captured rawBlocks i.val a s) at h
    cases h.unfold with
    | core step =>
      cases step with
      | follow_body _ localDiv => exact Or.inl ((nativeOrdinary entry blocks M _ .diverge).mpr localDiv)
      | follow_next _ head tail => exact Or.inr (diverges_after_eval entry blocks M head tail)

private theorem diverges_iff {p : Point R.length M.α M.σ} :
    (Finite graph p .diverge ∨ Infinite graph p) ↔
      External.Diverges M.instr M.prim (nativeConfig entry blocks M p) := by
  constructor
  · rintro (⟨q, path, finish⟩ | infinite)
    · induction path using Relation.ReflTransGen.head_induction_on with
      | refl =>
        have localDiv := (nativeOrdinary entry blocks M q .diverge).mp finish
        cases q with
        | entry s => exact External.Diverges.fold_core (.cfg_entry localDiv)
        | block i a s => exact External.Diverges.fold_core (.follow_body i.isLt localDiv)
      | head edge _ ih => exact External.Diverges.fold (step_config entry blocks M edge ih)
    · refine External.Diverges.coinduct
        (fun c => ∃ q, c = nativeConfig entry blocks M q ∧ Infinite graph q) ?_ ⟨p, rfl, infinite⟩
      rintro _ ⟨q, rfl, hq⟩
      obtain ⟨t, step, rest⟩ := infinite_unfold hq
      exact step_config entry blocks M step ⟨t, rfl, rest⟩
  · exact diverge_of_unfold
      (fun q => External.Diverges M.instr M.prim (nativeConfig entry blocks M q))
      (diverges_unfold entry blocks M)

theorem denote_native_feedback (s : M.σ) :
    denote (.feedback (.native entry) (fun i => .native (blocks i))) M s =
      denote (.native ⟨nativeFeedback entry blocks, nativeFeedback_hasType entry blocks⟩) M s := by
  have noTop (p : Point R.length M.α M.σ) : graph p ≠ ⊤ := by
    cases p <;> exact WithTop.coe_ne_top
  change close graph (.entry s) =
    WithTop.some (nativeOutcomes ⟨nativeFeedback entry blocks, nativeFeedback_hasType entry blocks⟩ M s)
  rw [close_of_noUB (fun ⟨q, _, top⟩ => noTop q top)]
  apply congrArg WithTop.some
  ext o
  rw [mem_nativeOutcomes_iff ⟨nativeFeedback entry blocks, nativeFeedback_hasType entry blocks⟩
    (M := M) (envOfBound_agrees M.bound)]
  cases o with
  | ret j a s' =>
    simpa only [outcomes, Set.mem_ofPred_eq, reduceCtorEq, false_and, or_false, Returns] using
      (finite_return_iff entry blocks M (p := .entry s) (j := j) (value := a) (s' := s'))
  | fault s' =>
    simpa only [outcomes, Set.mem_ofPred_eq, reduceCtorEq, false_and, or_false, Faults] using
      (finite_fault_iff entry blocks M (p := .entry s) (s' := s'))
  | diverge =>
    simpa only [outcomes, Set.mem_ofPred_eq, eq_self, true_and, nativeConfig] using
      (diverges_iff entry blocks M (p := .entry s))

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback
