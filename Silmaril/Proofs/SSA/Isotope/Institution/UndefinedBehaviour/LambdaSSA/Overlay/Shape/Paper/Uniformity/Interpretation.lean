module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Uniformity.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Uniformity.Forwarding
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Uniformity.Simulation
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Substitution
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Preservation
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Semantics.Reflection.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Uniformity

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.Region (ValueBranches liftLSubstVars)
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.Uniformity (localMap)
open Silmaril.Isotope.LambdaSSA.UB.Overlay (nativeOutcomes mem_nativeOutcomes_iff)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape (ValueTyped)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper (squareLeft squareRight uniformSource uniformTarget)
open Silmaril.Isotope.Morphism.SSAIter (envOfBound envOfBound_agrees)
open Silmaril.DeBruijn (lift)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation (Ops RegionAt PureValue Realizes)

universe u v w x

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)] {Γ L : List (Ty κ)}
  {A D : Ty κ} {a : LambdaSSA.Tm Φ} {entry p q : LambdaSSA.Region Φ}
  {α : Type w} {σ : Type x} {O : Ops Φ α σ} {env : Env α}

omit [HasTy Φ (Ty κ)] in
private theorem map_guards (ha : a.BranchValue (A :: Γ) D) :
    LambdaSSA.Region.LSubst.Forwards Γ (A :: L) (D :: L) (localMap a) := by
  intro i X hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    exact ⟨0, a, D, rfl, rfl, ha⟩
  | succ i => exact ⟨i + 1, .var 0, X, rfl, hi, .var rfl⟩

private noncomputable def stateMap (O : Ops Φ α σ) (env : Env α) (ha : a.BranchValue (A :: Γ) D)
    (v : Value α) : Value α :=
  (PureValue.ofBranchValue (O := O) (env := extend env v) ha).choose

omit [HasTy Φ (Ty κ)] in
private theorem map_route {O : Ops Φ α σ} (ha : a.BranchValue (A :: Γ) D) (i : Nat) (v : Value α) (s : σ)
    (j : Nat) (b : Value α) :
    exitRoute O.instr env (localMap a) i v s j b ↔
      j = i ∧ b = mapPayload (stateMap O env ha) i v := by
  cases i with
  | zero =>
    have pure : PureValue O (extend env v) a (stateMap O env ha v) :=
      (PureValue.ofBranchValue (O := O) (env := extend env v) ha).choose_spec
    constructor
    · intro run
      change Semantics.Region.Eval O.instr (extend env v) (.br 0 a) s j b s at run
      cases run with | br arg => exact ⟨rfl, (pure.unique arg).1⟩
    · rintro ⟨rfl, rfl⟩
      exact .br (pure.eval s)
  | succ i =>
    constructor
    · intro run
      change Semantics.Region.Eval O.instr (extend env v) (.br (i + 1) (.var 0)) s j b s at run
      cases run with | br arg => cases arg; exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩
      exact .br .var

omit [HasTy Φ (Ty κ)] in
private theorem observe_right {O : Ops Φ α σ} (ha : a.BranchValue (A :: Γ) D) (x : Value α) :
    RegionAt O (extend env x) ((.br 0 a : LambdaSSA.Region Φ).lsubst (liftLSubstVars (fun _ => q)))
      (extend env (stateMap O env ha x)) q := by
  let v := stateMap O env ha x
  have pure : PureValue O (extend env x) a v :=
    (PureValue.ofBranchValue (O := O) (env := extend env x) ha).choose_spec
  have inline := (Realizes.single pure).region (q.renameVars (lift Nat.succ))
  have agree (i : Nat) : extend (extend env x) v (lift Nat.succ i) = extend env v i := by
    cases i <;> rfl
  exact inline.trans {
    eval := Semantics.Region.Eval.renameVars_iff agree
    fault := Semantics.Region.Fault.renameVars_iff agree
    div := External.Diverges.renameVars_iff agree }

private abbrev operations {Δ : List (Ty κ)} (M : UB.Overlay.Shape.Model.{u,v,w,x} Φ Δ) :
    Ops Φ M.raw.α M.raw.σ := ⟨M.raw.instr, M.raw.faults, M.raw.prim⟩

private theorem denote_to_regionAt {Δ H : List (Ty κ)} (M : UB.Overlay.Shape.Model.{u,v,w,x} Φ Δ)
    {runtime : Env M.raw.α} (agree : Morphism.CaseSSA.EnvAgrees runtime M.raw.bound)
    (r t : UB.Typed (Φ := Φ) Δ H)
    (same : ∀ s, UB.Overlay.Shape.denote (.native r) M s = UB.Overlay.Shape.denote (.native t) M s) :
    RegionAt (operations M) runtime r.val runtime t.val := by
  have ordinary (s : M.raw.σ) : nativeOutcomes r M.raw s = nativeOutcomes t M.raw s :=
    WithTop.coe_inj.mp (same s)
  have iffAt (s : M.raw.σ) (o : UB.Overlay.Outcome H.length M.raw.α M.raw.σ) :=
    (mem_nativeOutcomes_iff r agree s o).symm.trans
      (((ordinary s) ▸ Iff.rfl : o ∈ nativeOutcomes r M.raw s ↔ o ∈ nativeOutcomes t M.raw s).trans
        (mem_nativeOutcomes_iff t agree s o))
  refine ⟨?_, ?_, ?_⟩
  · intro s j a t'
    constructor
    · intro run
      have bound := r.property.scoped.eval_label_lt run
      exact (iffAt s (.ret ⟨j, bound⟩ a t')).mp run
    · intro run
      have bound := t.property.scoped.eval_label_lt run
      exact (iffAt s (.ret ⟨j, bound⟩ a t')).mpr run
  · intro s t'; exact iffAt s (.fault t')
  · intro s; exact iffAt s .diverge

private theorem regionAt_to_denote {Δ H : List (Ty κ)} (M : UB.Overlay.Shape.Model.{u,v,w,x} Φ Δ)
    (r t : UB.Typed (Φ := Φ) Δ H) (s : M.raw.σ)
    (same : RegionAt (operations M) (envOfBound M.raw.bound) r.val (envOfBound M.raw.bound) t.val) :
    UB.Overlay.Shape.denote (.native r) M s = UB.Overlay.Shape.denote (.native t) M s := by
  simp only [UB.Overlay.Shape.denote, UB.Overlay.denote, WithTop.coe_inj]
  apply Set.ext
  intro o
  simp only [mem_nativeOutcomes_iff _ (envOfBound_agrees M.raw.bound)]
  cases o with
  | ret j a t => exact same.eval
  | fault t => exact same.fault
  | diverge => exact same.div

private theorem local_reply {O : Ops Φ α σ} {atomType : α → κ → Prop} {Δ : List (Ty κ)}
    (prim : Resumption.Typing.InstrTyped atomType O.instr)
    {runtime : Env α} (typed : UB.Overlay.Shape.EnvTyped atomType Δ runtime)
    {r : LambdaSSA.Region Φ} (hr : r.HasType Δ (A :: L))
    {start stop : σ} {v : Value α} (reply : Semantics.Region.Eval O.instr runtime r start 0 v stop) :
    ValueTyped atomType v A := by
  obtain ⟨B, label, value⟩ := region_eval_typed_at prim typed hr reply
  have same : A = B := Option.some.inj label
  exact same.symm ▸ value

theorem uniform_of_observed_square
    (he : ValueBranches Γ entry (A :: L)) (hp : ValueBranches (A :: Γ) p (A :: L))
    (hq : q.HasType (D :: Γ) (D :: L)) (ha : a.BranchValue (A :: Γ) D)
    (square : ∀ (M : UB.Overlay.Shape.Model.{u,v,w,x} Φ (A :: Γ)) (s : M.raw.σ),
      UB.Overlay.Shape.denote (.native (squareLeft hp ha)) M s =
      UB.Overlay.Shape.denote (.native (squareRight hq ha)) M s)
    (M : UB.Overlay.Shape.Model.{u,v,w,x} Φ Γ) (s : M.raw.σ) :
    UB.Overlay.Shape.denote (.native (uniformSource he hp)) M s =
      UB.Overlay.Shape.denote (.native (uniformTarget he hq ha)) M s := by
  let O := operations M
  let env := envOfBound M.raw.bound
  let f := stateMap O env ha
  let typed (x : Value M.raw.α) := ValueTyped M.atomType x A
  have mapsEntry : MappedAt O env env entry (entry.lsubst (localMap a)) f :=
    ((forwarding he (map_guards ha) O env).congr_route (map_route ha)).map_payload
  have mapsBody (x : Value M.raw.α) (hx : typed x) :
      MappedAt O (extend env x) (extend env (f x)) p q f := by
    have forwarded := forwarding hp (guard_capture (map_guards ha) A) O (extend env x)
    have routes := (forwarded.congr_route (lift_capture x)).congr_route (map_route (O := O) ha)
    have h := routes.map_payload
    have same := (denote_to_regionAt (M.extend hx) ((envOfBound_agrees M.raw.bound).extend x)
      (squareLeft hp ha) (squareRight hq ha) (square (M.extend hx))).trans (observe_right ha x)
    exact ⟨same.eval.symm.trans h.eval, same.fault.symm.trans h.fault, same.div.symm.trans h.div⟩
  have entryTyped {a s t} (run : Semantics.Region.Eval O.instr env entry s 0 a t) : typed a :=
    local_reply M.instrTyped (UB.Overlay.Shape.env_typed M) he.hasType run
  have closed {a b s t} (hx : typed a) (run : Semantics.Region.Eval O.instr (extend env a) p s 0 b t) :
      typed b := local_reply M.instrTyped ((UB.Overlay.Shape.env_typed M).extend hx) hp.hasType run
  exact regionAt_to_denote M (uniformSource he hp) (uniformTarget he hq ha) s
    (uniform_cfg mapsBody (fun hx run => closed hx run) mapsEntry (fun run => entryTyped run))

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Uniformity
