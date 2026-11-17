module

public import Silmaril.Wasm.Component.DecoderBridge.Multi.Defs
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Sim
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp.Read
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore.Main

/-!
# The start goal on `MultiImpFrag` from its four pieces

* `multiImpFrag_inv`: what the fragment says, unpacked;
* `nodes_ne_nil`: in the fragment, the IR reading has a first node;
* `startAdequacyFrag_of`: `Task.startAdequacyFrag` from `Task.nodeCallsIR`, `Task.firstNodeRef`,
  `Task.laterNodesRef` and `Task.exportRef`: the IR play splits into its node-by-node
  instantiation (`nodesInst_of_startPlay`) and the calls of each node (a); the first node takes
  the reference machine to the definitions after it with the log of its calls (b); the later
  nodes finish the instantiation with the log of theirs (c); the export call matches (d).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Conformance Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstTests Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Reference.Core3Adder (first)
open Silmaril.Wasm.SingleThreaded (profile neverFail)

theorem multiImpFrag_inv {r : RefComponent} (h : MultiImpFrag r) :
    FirstImpFrag r ∧ HostWired r ∧
      (∃ R, refRead r = some R ∧ lowWired R = true ∧
        (R.exports.head?.map fun e => isGetTy e.ty).getD false = true) ∧
      ∃ pre mi cargs post, firstCore? r = some (pre, mi, cargs, post) ∧ rootShape pre = true ∧
        post.all (postDefOk (preLowers pre) (preInsts pre) (coreMods pre)) = true := by
  unfold MultiImpFrag multiImpFrag at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hf, hw⟩, hR⟩, hp⟩ := h
  refine ⟨hf, hw, ?_, ?_⟩
  · split at hR
    · rename_i R hR'
      simp only [Bool.and_eq_true] at hR
      exact ⟨R, hR', hR.1, hR.2⟩
    · cases hR
  · split at hp
    · rename_i pre mi cargs post hs
      simp only [Bool.and_eq_true] at hp
      exact ⟨pre, mi, cargs, post, hs, hp.1, hp.2⟩
    · cases hp

/-- **In the fragment, the IR reading has a first node.** -/
theorem nodes_ne_nil {b : ByteArray} {c : Comp Binary.CoreMod} {r : RefComponent}
    {ps : List (Binary.CoreMod × List Impl)} (hc : Binary.parseComponent b = .ok c)
    (hr : decodeRef b = .ok r) (hf : MultiImpFrag r) (hn : c.nodes = coreNodes ps) :
    ∃ p ps', ps = p :: ps' := by
  obtain ⟨hfi, hw, -, pre, mi, cargs, post, hs, -, -⟩ := multiImpFrag_inv hf
  obtain ⟨R, hR, -, -, hN⟩ := relW_of_decode hc hr (inFrag_of_hostWired hw)
  have hpre : preOk 0 0 pre = true := by
    unfold FirstImpFrag firstImpFrag at hfi
    rw [hs] at hfi
    simp only [Bool.and_eq_true] at hfi
    exact hfi.1
  obtain ⟨m, w, -, -, -, -, hR0, -⟩ :=
    FirstImp.refRead_firstW (FirstCore.firstCore?_eq r hs) hpre hR
  have hl := hN.length_eq
  cases ps with
  | nil =>
    rw [hn] at hl
    cases hRn : R.nodes with
    | nil => rw [hRn] at hR0; cases hR0
    | cons x xs => rw [hRn] at hl; simp [coreNodes] at hl
  | cons p ps' => exact ⟨p, ps', rfl⟩

theorem logOfCalls_append (t t' : List (Σ _ : sigU.Op, Option Payload)) :
    logOfCalls (t ++ t') = logOfCalls t ++ logOfCalls t' := by
  simp [logOfCalls, List.filterMap_append]

/-- **The start goal on the fragment, from its four pieces.** -/
theorem startAdequacyFrag_of (ha : Task.nodeCallsIR) (hb : Task.firstNodeRef)
    (hc : Task.laterNodesRef) (hd : Task.exportRef) : Task.startAdequacyFrag := by
  intro b c r t n ws hpc hr hv hf himp hex hu hp
  obtain ⟨-, hw, -, pre, mi, cargs, post, hs, -, -⟩ := multiImpFrag_inv hf
  obtain ⟨ps, hnodes, hNI⟩ := nodesInst_of_startPlay hpc hr hw hp
  rw [himp] at hNI
  obtain ⟨ts, rfl, hF⟩ := ha b c r ps t hpc hr hf himp hnodes hu hNI
  obtain ⟨p, ps', rfl⟩ := nodes_ne_nil hpc hr hf hnodes
  cases hF with
  | @cons _ t₀ _ ts' h₀ hF' =>
    simp only [List.flatten_cons, List.mem_append] at hu
    obtain ⟨sc, M, hM⟩ := hb b c r p ps' t₀ pre mi cargs post hpc hr hf himp hnodes
      (fun x hx => hu x (.inl hx)) h₀ hs
    obtain ⟨M', inst, es, hI, hh⟩ := hc b c r p ps' ts' pre mi cargs post sc _ M hpc hr hf himp
      hnodes (fun x hx => hu x (.inr hx)) hF' hs hM
    obtain ⟨f, M'', hl, hS, hh'⟩ := hd b c r _ n ws M' inst es hpc hr hv hf himp hex
      (fun x hx => by
        simp only [List.flatten_cons, List.mem_append] at hx
        exact hu x hx) hp hI
    refine ⟨M', inst, es, [f], M'', hI, ?_, ?_, ?_⟩
    · simp [hl]
    · exact hS
    · rw [hh', hh, List.flatten_cons, logOfCalls_append]

/-- **The start goal on the fragment, from (a), the instantiation and (d).** -/
theorem startAdequacyFrag_of_nodes (ha : Task.nodeCallsIR) (hn : Task.nodesRef)
    (hd : Task.exportRef) : Task.startAdequacyFrag := by
  intro b c r t n ws hpc hr hv hf himp hex hu hp
  obtain ⟨-, hw, -, -⟩ := multiImpFrag_inv hf
  obtain ⟨ps, hnodes, hNI⟩ := nodesInst_of_startPlay hpc hr hw hp
  rw [himp] at hNI
  obtain ⟨ts, rfl, hF⟩ := ha b c r ps t hpc hr hf himp hnodes hu hNI
  obtain ⟨M', inst, es, hI, hh⟩ := hn b c r ps ts hpc hr hf himp hnodes hu hF
  obtain ⟨f, M'', hl, hS, hh'⟩ := hd b c r _ n ws M' inst es hpc hr hv hf himp hex hu hp hI
  refine ⟨M', inst, es, [f], M'', hI, ?_, ?_, ?_⟩
  · simp [hl]
  · exact hS
  · rw [hh', hh]

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi
