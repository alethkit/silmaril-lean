module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.Later
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.GapMachine

/-!
# A later core instantiation, in the shared core store (`LaterCoreStep`)

From the definitions `.coreInstance (.instantiate mi cargs) :: ds` with the machine invariant
`LaterInv`, an IR node of the module `m` that is ready after the calls `t`:

* the module's imports resolve to the first `b` trampolines of the shared core store `σ`
  (`coreImportsFor_shared`), and its preparation there is the IR's, mapped into `σ` along the gap
  `⟨σ, b⟩` (`prepareE_gap`);
* without a start function, the core instance is pushed at once (`t = []`);
* with one, the start call reaches the core activation (`start_atG`); the activation runs the IR's
  start run with its host calls in the shared store (`startRun_gapX`), returns no values, and the
  epilogue takes the machine back to the instantiation program;
* the core instance is pushed, and `LaterInv` holds again (`ι₁` after a start thread).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi

open Silmaril.Games Silmaril.Games.Inst
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp
open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Instantiate
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
  Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.Reference.Core3Adder (first)
open Silmaril.Wasm.SingleThreaded (GrowOracle Internal status neverFail profile)

local notation "Σh" => Unit × List HLinked2.HostEvent

/-! ## The fragment's facts on a later module -/

theorem postDefOk_core {n : Nat} {insts : List (List (String × Nat))}
    {mods : List Silmaril.Wasm.Module} {mi : Nat} {cargs : List (String × Nat)}
    {m : Silmaril.Wasm.Module} (hm : mods[mi]? = some m)
    (h : postDefOk n insts mods (.coreInstance (.instantiate mi cargs)) = true) :
    splitMod m = true ∧ irTypesOk m = true ∧ importsBelow cargs insts n m = true ∧
      importsLowered cargs insts m = true ∧ refTypesOk m = true ∧
      m.imports.all (fun i => match i.type with | .func _ => true | _ => false) = true := by
  simp only [postDefOk, hm, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- The imports of a later module are among the trampolines. -/
theorem imports_le {cargs : List (String × Nat)} {insts : List (List (String × Nat))} {n : Nat}
    {m : Silmaril.Wasm.Module} (hb : importsBelow cargs insts n m = true)
    (hl : importsLowered cargs insts m = true) : m.imports.length ≤ n := by
  rcases Nat.eq_zero_or_pos m.imports.length with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  have hi : m.imports.length - 1 < m.imports.length := by omega
  have hidx := importsLowered_get hl hi
  unfold importsBelow at hb
  have := List.all_eq_true.mp hb _ (List.getElem_mem hi)
  rw [hidx] at this
  simp only [decide_eq_true_eq] at this
  omega

/-! ## The component instance's thread table -/

theorem inst_round {ι : InstState} (h : InstOk ι) (t : ThreadId) :
    ∃ ι', ι.addThread? t = some (1, ι') ∧
      ι'.removeThread? 1 = some (t, InstState.removeThread 1 ι') ∧
      InstState.removeThread 1 ι' = ι₁ ∧ ι'.mayLeave = true := by
  rcases h with rfl | rfl
  · exact ⟨_, rfl, rfl, rfl, rfl⟩
  · exact ⟨_, rfl, rfl, rfl, rfl⟩

/-! ## The exports of a prepared instance -/

section Exports

open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- The shape of an export instance of the export `e`: its name, and a function address for a
function export. -/
def ExpShape (e : Silmaril.Wasm.Export) (x : ExportInst) : Prop :=
  x.name = e.name ∧ ∀ k, e.index = .func k → ∃ a : Nat, x.addr = .func a

theorem allocExport?_shape {mi : ModuleInst} {e : Silmaril.Wasm.Export} {x : ExportInst}
    (h : allocExport? mi e = some x) : ExpShape e x := by
  unfold allocExport? at h
  rcases e with ⟨nm, ix⟩
  cases ix <;> simp only [Option.map_map, Option.map_eq_some_iff, Function.comp_apply] at h <;>
    obtain ⟨a, -, rfl⟩ := h <;> refine ⟨rfl, fun k hk => ?_⟩ <;> cases hk
  exact ⟨a, rfl⟩

theorem allocModule?_exports {s s' : Store H} {m : Silmaril.Wasm.Module} {xas : List ExternAddr}
    {vG : List Silmaril.Wasm.Execution.Core.Val} {rT : List Ref} {rE : List (List Ref)} {mi : ModuleInst}
    (h : allocModule? s m xas vG rT rE = some (s', mi)) :
    List.Forall₂ ExpShape m.exports mi.exports := by
  unfold allocModule? at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨tagTypes, -, funcTypes, -, xi, hxi, he⟩ := h
  have hmi := (Prod.mk.inj he).2
  subst hmi
  refine List.forall₂_iff_get.mpr ⟨(List.mapM_eq_some_iff_forall₂.mp hxi).length_eq, ?_⟩
  intro i h₁ h₂
  exact allocExport?_shape ((List.mapM_eq_some_iff_forall₂.mp hxi).get h₁ h₂)

theorem prepare?_exports {s : Store H} {m : Silmaril.Wasm.Module} {xas : List ExternAddr}
    {c : Config H} {st : Option Silmaril.Wasm.FuncIdx}
    (h : prepare? evalConst? s m xas = some (c, st)) :
    List.Forall₂ ExpShape m.exports c.frame.module.exports := by
  unfold prepare? at h
  split_ifs at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i s₄ mi ha
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  exact allocModule?_exports ha

theorem instantiateOnce?_exports {s s' : Store H} {m : Silmaril.Wasm.Module}
    {xas : List ExternAddr} {f' : Frame} {st : Option Silmaril.Wasm.FuncIdx}
    (hseg : m.data = [] ∧ m.elems = []) (h : instantiateOnce? s m xas = some (s', f', st)) :
    List.Forall₂ ExpShape m.exports f'.module.exports := by
  unfold instantiateOnce? at h
  split at h
  · cases h
  unfold instantiateDirect? prepareDirect? at h
  split at h
  · cases h
  rename_i c st' hc
  have hseg' : m.globalResidue.data = [] ∧ m.globalResidue.elems = [] := hseg
  simp only [initSegments?, initElem?, initData?, hseg'.1, hseg'.2] at h
  obtain ⟨-, rfl, -⟩ := h
  exact prepare?_exports (m := m.globalResidue) hc

theorem prepareE?_exports {s s' : Store H} {m : Silmaril.Wasm.Module} {xas : List ExternAddr}
    {i : ModuleInst} {st : Option Nat} (hseg : m.data = [] ∧ m.elems = [])
    (h : Silmaril.Wasm.Component.Engine.Core3.prepareE? s m xas = some (s', i, st)) :
    List.Forall₂ ExpShape m.exports i.exports := by
  obtain ⟨mt, f', st₀, -, -, hi, rfl, -⟩ :=
    Silmaril.Wasm.Component.Engine.Core3.Typed.prepareE?_inv h
  exact instantiateOnce?_exports hseg hi

/-- The exports of the mapped instance, as the machine's core instance. -/
theorem instExports_minst (δ : GShift) {m : Silmaril.Wasm.Module} {mi : ModuleInst}
    (h : List.Forall₂ ExpShape m.exports mi.exports) :
    List.Forall₂ (fun (e : Silmaril.Wasm.Export) (x : String × (core3 neverFail).ExternVal) =>
        x.1 = e.name ∧ ∀ k, e.index = .func k → ∃ a : Nat, x.2 = ExternAddr.func a)
      m.exports ((core3 neverFail).exports (δ.minst mi)) := by
  show List.Forall₂ _ m.exports ((mi.exports.map δ.xinst).map fun x => (x.name, x.addr))
  rw [List.map_map]
  refine List.forall₂_map_right_iff.mpr (h.imp fun e x hx => ⟨hx.1, fun k hk => ?_⟩)
  obtain ⟨a, ha⟩ := hx.2 k hk
  refine ⟨δ.fn a, ?_⟩
  simp only [Function.comp_apply, GShift.xinst, ha, GShift.xa]
  rfl

end Exports

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi
