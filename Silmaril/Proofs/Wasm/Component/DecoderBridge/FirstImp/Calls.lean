module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp.Path
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp.Rest

/-!
# The first core instantiation with host calls

* `lowF_call`: an import call wired to the lowering `lowF` of `f: func(u32)` that is answered by
  one call of the component's imports is a call `f(u32 b)` for an `i32` argument `b`, and the
  answer `()` of `f` is answered to the core module with no results;
* `coreLog_eq`: so the host log of the IR's import calls (`coreLog`) is the log of the component
  calls (`InstRef.logOfCalls t`);
* `firstImp_setup`: the facts the fragment `FirstImpFrag` gives about the first node;
* `ref_firstImp_start`: when the IR's first node prepares and runs its start function with
  import calls to a returned status, the reference machine's instantiation reaches the core
  activation of the start function at that status, with the host log of the calls;
* `firstImp_failCalls_ref`, `firstImp_ready_ref`: the reference half for a first node that fails,
  or becomes ready, **after host calls** (`NodeCalls`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp

open Silmaril.Games Silmaril.Games.Inst
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore
open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Instantiate
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
  Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Reference.Core3Adder (first)
open Silmaril.Wasm.SingleThreaded (GrowOracle Internal status neverFail profile)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread

/-! ## The wiring of a host call -/

theorem liftArgs_u32 {xs : List Flat} {ws : List Silmaril.Wasm.Component.Val}
    (h : liftArgs [.u32] xs = some ws) :
    ∃ b : BitVec 32, xs = [⟨.int .i32, b⟩] ∧ ws = [.u32 b] := by
  rcases xs with _ | ⟨⟨ty, b⟩, _ | ⟨y, ys⟩⟩
  · simp [liftArgs, ValTy.liftList, ValTy.lift] at h
  · rcases ty with (_ | _ | _) | (_ | _) <;>
      simp [liftArgs, ValTy.liftList, ValTy.lift] at h
    · exact ⟨b, rfl, h.symm⟩
  · rcases ty with (_ | _ | _) | (_ | _) <;>
      simp [liftArgs, ValTy.liftList, ValTy.lift] at h

/-- **A host call through the lowering of `f`**: an import call answered by one call `x` of the
component's imports, with the answer `()`, is the call `f(u32 b)` of an `i32` argument `b`,
answered with no results. -/
theorem lowF_call {w : List Impl} {n : Nat} (hw : ∀ im ∈ w, im = lowF) {q : (sigN n).Op}
    (hq : q.1.val < w.length) {x : Σ _ : sigU.Op, Option Payload}
    {k : sigU.Ar x.1 → Prog sigU (Option Payload)} {r : Option Payload}
    (hc : implsN 1 w n q = .call x.1 k) (hk : k x.2 = .pure r) (hx : x.2 = some (.vals [])) :
    ∃ b : BitVec 32, q.2 = .flat [⟨.int .i32, b⟩] ∧ x.1 = (0, .vals [.u32 b]) ∧
      r = some (.flat []) := by
  have hget : w[q.1.val]? = some lowF := by
    rw [List.getElem?_eq_getElem hq, hw _ (List.getElem_mem hq)]
  obtain ⟨⟨j, hj⟩, pl⟩ := q
  obtain ⟨xq, xa⟩ := x
  simp only at hget hc hk hx ⊢
  subst hx
  simp only [implsN, implsH, hget, Impl.prog, runChain] at hc
  cases pl with
  | vals vs => simp [Adapter.down] at hc
  | flat xs =>
    cases hl : liftArgs [.u32] xs with
    | none => simp [Adapter.down, hl] at hc
    | some ws =>
      obtain ⟨b, rfl, rfl⟩ := liftArgs_u32 hl
      simp only [Adapter.down, hl, Option.map_some, Target.prog, Nat.zero_lt_one, ↓reduceIte] at hc
      injection hc with h₁ h₂
      subst h₁
      subst h₂
      refine ⟨b, rfl, rfl, ?_⟩
      simp only [Games.Prog.bind] at hk
      injection hk with hk
      rw [← hk]
      rfl

/-- **The host log of the IR's import calls is the log of the component calls.** -/
theorem coreLog_eq {w : List Impl} {n : Nat} (hw : ∀ im ∈ w, im = lowF) (hn : n ≤ w.length) :
    ∀ {ys : List (Σ _ : (sigN n).Op, Option Payload)} {t : List (Σ _ : sigU.Op, Option Payload)},
      List.Forall₂ (fun y x => ∃ k, implsN 1 w n y.1 = .call x.1 k ∧ k x.2 = .pure y.2) ys t →
      (∀ x ∈ t, x.2 = InstTests.unitV) →
      coreLog ys = logOfCalls t ∧ ∀ y ∈ ys, y.2 = some (.flat [])
  | [], [], .nil, _ => ⟨rfl, fun _ h => by cases h⟩
  | y :: ys, x :: t, .cons ⟨k, hc, hk⟩ hrest, hu => by
    obtain ⟨b, hy, hx, hr⟩ := lowF_call hw (by have := y.1.1.isLt; omega) hc hk
      (hu x List.mem_cons_self)
    obtain ⟨h₁, h₂⟩ := coreLog_eq hw hn hrest (fun x' hx' => hu x' (List.mem_cons_of_mem _ hx'))
    refine ⟨?_, ?_⟩
    · have ex : x = ⟨(0, .vals [.u32 b]), some (.vals [])⟩ := by
        obtain ⟨x1, x2⟩ := x
        simp only at hx
        subst hx
        have := hu _ List.mem_cons_self
        simp only [InstTests.unitV] at this
        subst this
        rfl
      subst ex
      simp only [coreLog, logOfCalls, List.filterMap_cons, coreEvent, hy] at h₁ ⊢
      rw [h₁]
      rfl
    · intro y' hy'
      rcases List.mem_cons.mp hy' with rfl | hy'
      · exact hr
      · exact h₂ y' hy'

end Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp
