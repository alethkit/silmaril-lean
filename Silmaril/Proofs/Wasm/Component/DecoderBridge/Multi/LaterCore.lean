module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.Nodes
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

/-! ## The step -/

open Silmaril.Proofs.Wasm.Component.Reference (storeGood_once storeGood_mapH_iff splitGood_invoke
  instantiateOnce?_noStart)

theorem preOk_extend (g : Gap (CanonHost (core3 neverFail))) {fs new : List (Silmaril.Wasm.Execution.Core.FuncInst (CanonHost (core3 neverFail)))}
    (h : g.PreOk fs) : g.PreOk (fs ++ new) := by
  refine ⟨by simp only [List.length_append]; have := h.1; omega, fun a ha => ?_⟩
  rw [h.2 a ha, List.getElem?_append_left (Nat.lt_of_lt_of_le ha h.1)]

/-- **A later core instantiation, in the shared core store.** -/
theorem laterCoreStep' : LaterCoreStep' := by
  intro pre mi cargs ds sc M m p t L K hmi hok hmod hilen hno hq hu hI hctl hhost
  obtain ⟨hsplit, hit, hbelow, hlow, hrt, hfun⟩ := postDefOk_core hmi hok
  have hle := imports_le hbelow hlow
  have hseg : m.data = [] ∧ m.elems = [] := by
    simp only [splitMod, Bool.and_eq_true, List.isEmpty_iff] at hsplit
    exact ⟨hsplit.1.2, hsplit.2⟩
  obtain ⟨ys, hEI, hF⟩ := hq
  obtain ⟨hlog, hans⟩ := coreLog_eq hno.wires hno.wl hF hu
  change EngineInst (core3P (profile neverFail))
    (Param.instOfI (core3P (profile neverFail)) (Binary.coreModule p.1) (CoreModule.imports p.1)
      (CoreModule.exports p.1)) (CoreModule.imports p.1) ys _ at hEI
  have hnames := hno.names
  rw [hmod] at hEI hnames
  obtain ⟨-, hsome⟩ := instOfI_cases hno.imps hnames
  obtain ⟨J, hJ, hstart⟩ := hEI
  obtain ⟨mi₂, hp⟩ := hsome J hJ
  rw [hilen] at hp
  -- the gap of the shared store
  let g : Gap (CanonHost (core3 neverFail)) := ⟨M.store.core, m.imports.length⟩
  have htr : ∀ i, i < g.b → g.pre.funcs[i]? = some (lowFI lowH) :=
    fun i hi => hI.tramp i (Nat.lt_of_lt_of_le hi hle)
  have hP₀ := preOk_irStore g htr
  have hinj : Function.Injective g.sh.fn := fnMap_injective g (PreOk.le_pre g hP₀)
  have hmd : sc.frame.coreModule? mi = some m := by
    simp only [Frame.coreModule?, hI.mods]
    exact hmi
  have hci := coreImportsFor_shared (o := neverFail) (s := M.store.core) (h := lowH) hI.insts
    (fun i hi => hI.tramp i (Nat.lt_of_lt_of_le hi hle)) hlow hrt
  cases hv : Silmaril.Wasm.Validation.validate? m with
  | none =>
    exfalso
    unfold Core3.prepareE? at hp
    rw [hv] at hp
    cases hp
  | some mt =>
  rw [importTypesE_length hv] at hci
  have hpg := prepareE_gap g htr hseg
  rw [hp] at hpg
  have hpr : (core3 neverFail).prepare? M.store.core m
      ((List.range m.imports.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func) =
      some (g.rel (Store.mapH FirstImp.gL J.store), g.sh.minst mi₂, J.start.map g.sh.fn) := hpg
  -- the typing of the shared store after the preparation
  obtain ⟨hsJ, -, ⟨newJ, hnewJ, hwasmJ⟩, hcfgJ⟩ :=
    Silmaril.Wasm.Component.Engine.Core3.Typed.prepareE?_typed hI.ok hpg
  have hHT : HostTy (g.rel (Store.mapH FirstImp.gL J.store)) := by
    intro fi hfi h hcode
    rw [hnewJ] at hfi
    rcases List.mem_append.mp hfi with hfi | hfi
    · exact hI.hosts fi hfi h hcode
    · obtain ⟨c, hc⟩ := hwasmJ fi hfi
      rw [hc] at hcode
      cases hcode
  have hfunsJ : ∀ i, i < preLowers pre →
      (g.rel (Store.mapH FirstImp.gL J.store)).funcs[i]? = some (lowFI lowH) := by
    intro i hi
    have h₀ := hI.tramp i hi
    rw [hnewJ, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h₀).1]
    exact h₀
  -- the exports of the new core instance
  have hexps := instExports_minst g.sh (prepareE?_exports hseg hp)
  -- the program at the core instantiation
  have hX : (List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc
      (Syntax.Definition.coreInstance (.instantiate mi cargs) :: ds) >>= K) =
      (instantiateCore ⟨0⟩ sc.frame mi cargs >>= fun es =>
        (pushEntry sc.frame (.core .instance_) (.coreInstance es) >>= fun f =>
          pure ({ sc with frame := f } : Scope (core3 neverFail))) >>= fun sc =>
        List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc ds >>= K) := by
    erw [List.foldlM_cons]
    simp only [instantiateDef, bind_assoc]
  have hM : M = { M with ctl := ⟨none, .prog (instantiateCore ⟨0⟩ sc.frame mi cargs >>= fun es =>
        (pushEntry sc.frame (.core .instance_) (.coreInstance es) >>= fun f =>
          pure ({ sc with frame := f } : Scope (core3 neverFail))) >>= fun sc =>
        List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc ds >>= K), []⟩ :: [] } := by
    obtain ⟨S, h₀, conts, ctl, pending, results, cancels⟩ := M
    simp only at hctl ⊢
    rw [hctl, ← hX]
    rfl
  have hpush : ∀ (es : List (String × (core3 neverFail).ExternVal))
      (m₂ : Machine.Config (core3 neverFail) Σh),
      RunsQ (DG embL.host) none (pushEntry sc.frame (.core .instance_) (.coreInstance es) >>= fun f =>
        pure ({ sc with frame := f } : Scope (core3 neverFail))) m₂ []
        ({ sc with frame := { sc.frame with coreInstances := sc.frame.coreInstances ++ [es] } } :
          Scope (core3 neverFail)) m₂ := by
    intro es m₂
    simp only [pushEntry, need, orTrap, Frame.push, pure_bind]
    exact .pure _ _
  have hinsts' : ∀ es : List (String × (core3 neverFail).ExternVal),
      ∃ X : List (List (String × Silmaril.Wasm.Execution.Core.ExternAddr)),
        sc.frame.coreInstances ++ [es] = (instsVal (preInsts pre) ++ X :
          List (List (String × Silmaril.Wasm.Execution.Core.ExternAddr))) := by
    intro es
    obtain ⟨X, hX⟩ := hI.insts
    refine ⟨X ++ [show List (String × Silmaril.Wasm.Execution.Core.ExternAddr) from es], ?_⟩
    rw [hX]
    exact List.append_assoc _ _ _
  rcases hstart with ⟨hnone, rfl⟩ | ⟨f, c', fvs, hfs, hrun, hst⟩
  · -- no start function
    have ht : t = [] := by cases hF; rfl
    subst ht
    rw [hnone] at hpr
    have hcore' : RunsQ (DG embL.host) none (instantiateCore ⟨0⟩ sc.frame mi cargs) M
        [.tau, .tau] ((core3 neverFail).exports (g.sh.minst mi₂))
        { M with store := setCoreSt (g.rel (Store.mapH FirstImp.gL J.store)) M.store } := by
      unfold instantiateCore
      simp only [hmd, need, orTrap]
      refine RunsQ.bind (tr₁ := []) (.pure _ _) ?_
      refine RunsQ.bind (tr₁ := [.tau]) (.get (.pure _ _)) ?_
      rw [hci]
      refine RunsQ.bind (tr₁ := []) (.pure _ _) ?_
      erw [hpr]
      exact RunsQ.bind (tr₁ := [.tau])
        (.modify (f := setCoreSt (E := core3 neverFail) (g.rel (Store.mapH FirstImp.gL J.store)))
          rfl (.pure _ _))
        (.pure _ _)
    have d := RunsQ.lrun_at (prof := first.prof) (hr := embL.hr)
      (RunsQ.bind (f := fun es =>
          pushEntry sc.frame (.core .instance_) (.coreInstance es) >>= fun f =>
            pure ({ sc with frame := f } : Scope (core3 neverFail))) hcore' (hpush _ _))
      hI.lock
      (fun sc => List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc ds >>= K)
      (segs := []) (rest := []) (by rw [hM]; simp only [bind_assoc])
    refine ⟨_, _, _, _, d, Adequacy.LRun.no_host d,
      Adequacy.LRun.no_trap d ⟨List.cons_ne_nil _ _, hI.lock⟩, rfl, ⟨hI.mods, hinsts' _,
        hI.lock, hI.func0, hI.inst, hfunsJ, hsJ, hHT⟩, by rw [hhost]; simp [logOfCalls],
      rfl, rfl, rfl, rfl, hexps, rfl, rfl⟩
  · -- a start function
    rw [hfs] at hpr
    have hrun' : Param.StartRunI (core3P (profile neverFail)) (CoreModule.imports p.1)
        (J.store, Silmaril.Wasm.SingleThreaded.Thread.invoke f []) ys c' := hrun
    sorry


end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi
