module

public import Silmaril.Wasm.Component.InstTestsRef.Defs
public import Silmaril.Proofs.Wasm.Component.InstRef.Ref

/-!
# Component test binaries on the reference machine: runs

Kernel evaluations (`decide +kernel`) of the reference machine's executable drivers, turned into
behaviours by their soundness theorems:

* `starts_ref`: under the logging host, `startsRef` instantiates, its host log is
  `[f(1) ↦ (), f(2) ↦ ()]`, and `get()` then returns `42` (`LinkedSession.sessSummary`,
  `sessSummary_sound`);
* `trap_ref`: the instantiation of `trapRef` from the host functions' store traps
  (`trapSummaryL`, `traps_of_summaryL`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.InstTestsRef

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstTests Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Reference.Core3Adder (first)

/-- The host log of `starts`: `f(u32 1)` and `f(u32 2)`, each answered `()`. -/
def startsLog : List HLinked2.HostEvent :=
  [(⟨0⟩, [toRefVal (.u32 1)], []), (⟨0⟩, [toRefVal (.u32 2)], [])]

theorem starts_summary' :
    (LinkedSession.sessSummary embL first 400 startsRef hostI ((), []) [("get", [])]).map
      (fun p => (p.1, p.2.2)) = some ([some [toRefVal (.u32 42)]], startsLog) := by
  decide +kernel

theorem starts_summary :
    LinkedSession.sessSummary embL first 400 startsRef hostI ((), []) [("get", [])] =
      some ([some [toRefVal (.u32 42)]], ((), startsLog)) := by
  obtain ⟨⟨outs, u, log⟩, h, he⟩ := Option.map_eq_some_iff.1 starts_summary'
  cases u
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact h

theorem starts_ref :
    (([some [toRefVal (.u32 42)]] : List (Option (List Value.Val))), ((), startsLog)) ∈
      LinkedSession.sessRunBehaviours first.prof (Host.ofEmbedder embL) ((), []) startsRef
        hostI [("get", [])] :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSession.sessSummary_sound starts_summary

section Trap

open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon

/-- The instantiation of `c` from the host functions' store of `ims`, with import `k` bound to
host function `k`, traps without an `internal` fault within `fuel` steps of the logging
embedder `embL`. -/
def trapSummaryL (fuel : Nat) (c : Core3Component) (ims : Iface) : Bool :=
  match hostStep? embL.hr (instantiateTop c (importArgs ims)) (LinkedSession.hostConfig ims ((), [])) with
  | none => false
  | some (_, m₁) =>
    let r := Machine.run embL.hr embL.dispatch embL.X first fuel m₁
    decide (r.outcome = .trap) && !(r.labels.any Label.isInternalTrap)

/-- A trapping summary is a trapping instantiation of the reference machine. -/
theorem traps_of_summaryL {fuel : Nat} {c : Core3Component} {ims : Iface}
    (h : trapSummaryL fuel c ims = true) :
    InstResult.traps ∈ instBehaviours first.prof (Host.ofEmbedder embL)
      (LinkedSession.hostConfig ims ((), [])) c (importArgs ims) := by
  unfold trapSummaryL at h
  split at h
  next => cases h
  next l m₁ e =>
    have ho : (Machine.run embL.hr embL.dispatch embL.X first fuel m₁).outcome = .trap ∧
        (Machine.run embL.hr embL.dispatch embL.X first fuel m₁).labels.any
          Label.isInternalTrap = false := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true]
        using h
    have hl : l = .host (instantiateTop c (importArgs ims)) := hostStep?_run_label e
    have s₁ := hostStep?_sound first.prof embL.hr embL.dispatch e
    have hs := Machine.run_sound embL.hr embL.dispatch embL.X first fuel m₁
    have hT : Trapped (Machine.run embL.hr embL.dispatch embL.X first fuel m₁).config := by
      rcases Machine.run_outcome embL.hr embL.dispatch embL.X first fuel m₁ with e' | e'
      · exact absurd (e'.symm.trans ho.1) (by decide)
      · exact outcomeOf_trap _ (e' ▸ ho.1)
    refine ⟨_, _, hl ▸ Steps.cons s₁ hs, run_noHost _ _ _ _ _ _, fun msg hm => ?_, hT⟩
    have hany : (Machine.run embL.hr embL.dispatch embL.X first fuel m₁).labels.any
        Label.isInternalTrap = true :=
      List.any_eq_true.mpr ⟨_, hm, Label.isInternalTrap_trap_internal msg⟩
    exact absurd (hany.symm.trans ho.2) (by decide)

end Trap

theorem trap_ref : InstResult.traps ∈ instBehaviours first.prof (Host.ofEmbedder embL)
    (LinkedSession.hostConfig hostI ((), [])) trapRef (importArgs hostI) :=
  traps_of_summaryL (fuel := 400) (by decide +kernel)

end Silmaril.Proofs.Wasm.Component.InstTestsRef
