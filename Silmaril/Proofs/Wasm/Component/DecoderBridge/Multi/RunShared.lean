module

public import Silmaril.Wasm.Component.DecoderBridge.MultiX.Defs
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.GapMachine
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.Compose
public import Silmaril.Proofs.Wasm.Component.Reference.SplitInit
public import Silmaril.Proofs.Wasm.Game.Machine.Profile

/-!
# A node's run in the shared core store (`Task.coreRunShared`)

The IR runs an exported function of node `j` alone, from the store its start function left. The
reference machine runs the relocated function in the shared core store: the node's store relocated
along the gap `g` (`Gap.rel`), followed by the objects `U` of later nodes.

* `OwnOk O t`: what `O` owns exists in `t` and is good (the store half of
  `Linking.Split.PartRel`); it is transported to the gap image (`Own.gap`, `OwnOk.gap`), and gives
  the identity `PartRel` of a store with the store extended by `U` (`OwnOk.partRel_app`);
* `steps_part`: host-free runs along `Linking.Split.step_sim` (fresh structures and arrays may be
  renamed: in the shared store they land past `U`);
* `RunInv`, `startRun_inv`: the start run (with its import calls) keeps a split invariant whose
  ownership covers every function of the store;
* `runShared`: the run in the shared store, then the interpreter run (`runCI_complete`, typed by
  the shared store's typing and the callee's type, read off the IR run's first step);
* **`coreRunShared`**: `Task.coreRunShared`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel noHost step_sim Ren.id)
open Silmaril.Proofs.Wasm.Component.Reference (SplitGood Store.app ownOf StoreGood Store.mapH
  FuncInst.mapH)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-! ## Owned objects of a store -/

/-- **What `O` owns exists in `t` and is good** (the store half of `PartRel`). -/
structure OwnOk (O : Own) (t : Store H) : Prop where
  fn : ∀ a, O.fn a → ∃ fi, t.funcs[a]? = some fi ∧ ∀ c, fi.code = .wasm c → O.ModGood fi.module
  gl : ∀ a, O.gl a → ∃ g, t.globals[a]? = some g ∧ O.GoodVal g.value
  st : ∀ a, O.st a → ∃ si, t.structs[a]? = some si ∧ ∀ fv ∈ si.fields, O.GoodFV fv
  ar : ∀ a, O.ar a → ∃ ai, t.arrays[a]? = some ai ∧ ∀ fv ∈ ai.fields, O.GoodFV fv

theorem ownOk_of_partRel {ρ : Ren} {O : Own} {p σ : Store H} (h : PartRel ρ O p σ) : OwnOk O p where
  fn a ha := by
    obtain ⟨fi, h1, fi', _, _, h4⟩ := h.fn a ha
    exact ⟨fi, h1, fun c hc => (h4 c hc).2⟩
  gl a ha := by
    obtain ⟨g, h1, -, h3⟩ := h.gl a ha
    exact ⟨g, h1, h3⟩
  st a ha := by
    obtain ⟨si, h1, -, h3⟩ := h.st a ha
    exact ⟨si, h1, h3⟩
  ar a ha := by
    obtain ⟨ai, h1, -, h3⟩ := h.ar a ha
    exact ⟨ai, h1, h3⟩

theorem getElem?_app_left {α : Type} {l l' : List α} {a : Nat} {x : α} (h : l[a]? = some x) :
    (l ++ l')[a]? = some x := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

/-- **A store with good owned objects is related to itself extended by `U`**, by the identity. -/
theorem OwnOk.partRel_app {O : Own} {t : Store H} (h : OwnOk O t) (U : Store H) :
    PartRel Ren.id O t (Store.app t U) where
  fn a ha := by
    obtain ⟨fi, h1, h2⟩ := h.fn a ha
    exact ⟨fi, h1, fi, getElem?_app_left h1, rfl, fun c hc => ⟨rfl, h2 c hc⟩⟩
  gl a ha := by
    obtain ⟨g, h1, h2⟩ := h.gl a ha
    exact ⟨g, h1, by simpa [Store.app] using getElem?_app_left (l' := U.globals) h1, h2⟩
  st a ha := by
    obtain ⟨si, h1, h2⟩ := h.st a ha
    exact ⟨si, h1, by simpa [Store.app] using getElem?_app_left (l' := U.structs) h1, h2⟩
  ar a ha := by
    obtain ⟨ai, h1, h2⟩ := h.ar a ha
    exact ⟨ai, h1, by simpa [Store.app] using getElem?_app_left (l' := U.arrays) h1, h2⟩
  stInj _ _ _ _ h := h
  arInj _ _ _ _ h := h

section MapH

variable {H' : Type} (f : H → H')

theorem OwnOk.mapH {O : Own} {t : Store H} (h : OwnOk O t) : OwnOk O (Store.mapH f t) where
  fn a ha := by
    obtain ⟨fi, h1, h2⟩ := h.fn a ha
    refine ⟨FuncInst.mapH f fi, ?_, fun c hc => h2 c ?_⟩
    · simp [Store.mapH, h1]
    · exact (Silmaril.Proofs.Wasm.Component.Reference.FuncCode.mapH_eq_wasm f).mp hc
  gl := h.gl
  st := h.st
  ar := h.ar

end MapH

/-! ## The gap image of an ownership -/

/-- The image of an ownership along the gap `g`. -/
def Own.gap (g : Gap H) (O : Own) : Own :=
  ⟨fun a' => ∃ a, O.st a ∧ a' = g.pre.structs.length + a,
    fun a' => ∃ a, O.ar a ∧ a' = g.pre.arrays.length + a,
    fun a' => ∃ a, O.fn a ∧ a' = g.fnMap a,
    fun a' => ∃ a, O.gl a ∧ a' = g.pre.globals.length + a⟩

section Gap

variable (g : Gap H) {O : Own}

theorem goodRef_gap : ∀ {r : Ref}, O.GoodRef r → (Own.gap g O).GoodRef (g.sh.ref r)
  | .i31 _, _ => trivial
  | .null, _ => trivial
  | .struct a, h => ⟨a, h, rfl⟩
  | .array a, h => ⟨a, h, rfl⟩
  | .func a, h => ⟨a, h, rfl⟩
  | .exn _, h => h.elim
  | .host _, h => h.elim
  | .extern r, h => goodRef_gap (r := r) h

theorem goodVal_gap {v : Val} (h : O.GoodVal v) : (Own.gap g O).GoodVal (g.sh.val v) := by
  cases v with
  | ref r => exact goodRef_gap g h
  | num => trivial
  | vec => trivial

theorem goodFV_gap {fv : FieldVal} (h : O.GoodFV fv) : (Own.gap g O).GoodFV (g.sh.fval fv) := by
  cases fv with
  | val v => exact goodVal_gap g h
  | pack => trivial

theorem modGood_gap {m : ModuleInst} (h : O.ModGood m) : (Own.gap g O).ModGood (g.sh.minst m) where
  tags := by simp [GShift.minst, h.tags]
  mems := by simp [GShift.minst, h.mems]
  tables := by simp [GShift.minst, h.tables]
  elems := by simp [GShift.minst, h.elems]
  datas := by simp [GShift.minst, h.datas]
  globals x hx := by
    simp only [GShift.minst_globals, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, h.globals y hy, rfl⟩
  funcs x hx := by
    simp only [GShift.minst_funcs, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, h.funcs y hy, rfl⟩

/-- **Owned objects along the gap.** -/
theorem OwnOk.gap {t : Store H} (hP : g.PreOk t.funcs) (h : OwnOk O t) :
    OwnOk (Own.gap g O) (g.rel t) where
  fn a' ha' := by
    obtain ⟨a, ha, rfl⟩ := ha'
    obtain ⟨fi, h1, h2⟩ := h.fn a ha
    exact ⟨g.sh.finst fi, funcs_gap_of g hP h1, fun c hc => modGood_gap g (h2 c hc)⟩
  gl a' ha' := by
    obtain ⟨a, ha, rfl⟩ := ha'
    obtain ⟨gi, h1, h2⟩ := h.gl a ha
    refine ⟨g.sh.ginst gi, ?_, goodVal_gap g h2⟩
    rw [rel_globals, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.getElem?_map, h1]
    rfl
  st a' ha' := by
    obtain ⟨a, ha, rfl⟩ := ha'
    obtain ⟨si, h1, h2⟩ := h.st a ha
    refine ⟨g.sh.sinst si, by rw [structs_gap, h1]; rfl, fun fv hfv => ?_⟩
    simp only [GShift.sinst, List.mem_map] at hfv
    obtain ⟨fv₀, hfv₀, rfl⟩ := hfv
    exact goodFV_gap g (h2 fv₀ hfv₀)
  ar a' ha' := by
    obtain ⟨a, ha, rfl⟩ := ha'
    obtain ⟨ai, h1, h2⟩ := h.ar a ha
    refine ⟨g.sh.ainst ai, by rw [arrays_gap, h1]; rfl, fun fv hfv => ?_⟩
    simp only [GShift.ainst, List.mem_map] at hfv
    obtain ⟨fv₀, hfv₀, rfl⟩ := hfv
    exact goodFV_gap g (h2 fv₀ hfv₀)

end Gap

/-! ## Invocations and runs -/

/-- **The invocation of an owned function, without arguments, is a good thread.** -/
theorem invoke_good_of {O : Own} {t : Store H} {a : Nat} (ha : O.fn a) :
    O.FrameGood (invoke t a []).frame ∧ O.CodeGood (invoke t a []).code := by
  refine ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, nofun, nofun⟩, nofun⟩, ?_⟩
  refine O.codeGood_append.mpr ⟨O.codeGood_vals.mpr nofun, ?_⟩
  exact Silmaril.Proofs.Wasm.Game.Linking.Split.Own.CodeGood.cons_ref ha (by simp [Own.CodeGood])

/-- **Host-free runs in the shared store, along `Linking.Split.step_sim`.** -/
theorem steps_part {P : Profile} {c c' : Config H}
    (h : Relation.ReflTransGen (Step P noHost) c c') {ρ : Ren} {O : Own} {σ : Store H}
    (hR : PartRel ρ O c.store σ) (hf : O.FrameGood c.frame) (hc : O.CodeGood c.code) :
    ∃ (ρ' : Ren) (O' : Own) (σ' : Store H),
      Relation.ReflTransGen (Step P noHost) ⟨σ, ρ.frame c.frame, ρ.code c.code⟩
        ⟨σ', ρ'.frame c'.frame, ρ'.code c'.code⟩ ∧
      PartRel ρ' O' c'.store σ' ∧ O'.FrameGood c'.frame ∧ O'.CodeGood c'.code := by
  induction h with
  | refl => exact ⟨ρ, O, σ, .refl, hR, hf, hc⟩
  | tail _ hst ih =>
    obtain ⟨ρ₁, O₁, σ₁, hrun, hR₁, hf₁, hc₁⟩ := ih
    obtain ⟨ρ₂, O₂, σ₂, hs, hR₂, hf₂, hc₂, -⟩ := step_sim hst hR₁ hf₁ hc₁
    exact ⟨ρ₂, O₂, σ₂, hrun.tail hs, hR₂, hf₂, hc₂⟩

/-! ## The start run keeps a split invariant -/

/-- **A split configuration whose ownership covers every function of its store.** -/
def RunInv (c : Config H) : Prop :=
  ∃ (ρ : Ren) (O : Own) (σ : Store H), PartRel ρ O c.store σ ∧ O.FrameGood c.frame ∧
    O.CodeGood c.code ∧ ∀ a, a < c.store.funcs.length → O.fn a

theorem RunInv.step {P : Profile} {c c' : Config H} (h : Step P noHost c c') (hg : RunInv c) :
    RunInv c' := by
  obtain ⟨ρ, O, σ, hR, hf, hc, hfn⟩ := hg
  obtain ⟨ρ', O', σ', -, hR', hf', hc', hG, -⟩ := step_sim h hR hf hc
  have hfs := (Silmaril.Wasm.SingleThreaded.Step.framesLocal h).1
  refine ⟨ρ', O', σ', hR', hf', hc', fun a ha => ?_⟩
  rw [hG.fn]
  exact hfn a (by rw [← hfs]; exact ha)

theorem RunInv.steps {P : Profile} {c c' : Config H}
    (h : Relation.ReflTransGen (Step P noHost) c c') (hg : RunInv c) : RunInv c' := by
  induction h with
  | refl => exact hg
  | tail _ hst ih => exact RunInv.step hst ih

/-- **Resuming with a result of good code keeps the invariant.** -/
theorem RunInv.resume {s : Store H} {t : Silmaril.Wasm.SingleThreaded.Thread}
    (hg : RunInv (t.config s)) {r : Silmaril.Wasm.SingleThreaded.CallResult}
    (hr : ∀ O : Own, O.CodeGood r.toAdmin) :
    RunInv ((Silmaril.Wasm.SingleThreaded.resume s t r).config s) := by
  cases hd : Silmaril.Wasm.SingleThreaded.decompose? s (t.config s).code with
  | none =>
    unfold Silmaril.Wasm.SingleThreaded.resume
    simp only [hd]
    exact hg
  | some q =>
    obtain ⟨E, a, h, args⟩ := q
    obtain ⟨ρ, O, σ, hR, hf, hc, hfn⟩ := hg
    obtain ⟨-, yy, -, -, -, -, -, -, -, hX⟩ := Silmaril.Wasm.SingleThreaded.decompose?_sound hd
    unfold Silmaril.Wasm.SingleThreaded.resume
    simp only [hd]
    refine ⟨ρ, O, σ, ?_, hf, ?_, ?_⟩
    · simpa [Silmaril.Wasm.SingleThreaded.Thread.config_store] using hR
    · exact Silmaril.Proofs.Wasm.Game.Linking.Split.Own.CodeGood.fill E
        (xs := vals args ++ [.ref (.func a), yy]) (by rw [← hX]; exact hc) (hr O)
    · simpa [Silmaril.Wasm.SingleThreaded.Thread.config_store] using hfn

theorem codeGood_toCR (O : Own) (r : Silmaril.Wasm.Component.Engine.CallResult) :
    O.CodeGood (Silmaril.Wasm.Component.Engine.Core3.toCR r).toAdmin := by
  cases r with
  | values vs =>
    refine O.codeGood_vals.mpr fun v hv => ?_
    simp only [List.mem_map] at hv
    obtain ⟨w, -, rfl⟩ := hv
    trivial
  | trap => simp [Silmaril.Wasm.Component.Engine.Core3.toCR,
      Silmaril.Wasm.SingleThreaded.CallResult.toAdmin, Own.CodeGood]

open Silmaril.Wasm.Component Silmaril.Wasm.Component.DecoderBridge in
/-- **The IR's start run (with its import calls) keeps the invariant.** -/
theorem startRun_inv {imps : CoreIface} {c c' : irEng.Config Nat}
    {ys : List (Σ _ : (sigN imps.length).Op, Option Payload)}
    (h : Param.StartRunI irEng imps c ys c') (hg : RunInv (c.2.config c.1)) :
    RunInv (c'.2.config c'.1) := by
  induction h with
  | nil run =>
    unfold Engine.CoreEngine.Steps at run
    rw [internalP_eqN] at run
    exact RunInv.steps (FirstCore.steps_of_internal run) hg
  | call run callout hh r rest ih =>
    unfold Engine.CoreEngine.Steps at run
    rw [internalP_eqN] at run
    have h₁ := RunInv.steps (FirstCore.steps_of_internal run) hg
    exact ih (RunInv.resume h₁ (fun O => codeGood_toCR O _))

/-! ## The node's store after its start run -/

section Node

open Silmaril.Wasm.Component Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp (irStore)
open Silmaril.Proofs.Wasm.Component.Reference (storeGood_once splitGood_invoke invoke_good
  instantiateOnce?_noStart)

/-- **The store a node's start function leaves is split**: some ownership owns every function and
its owned objects are good. -/
theorem nodeEnd_own {n : Nat} {cm : Binary.CoreMod} {args : List Impl} {x : NodeRun}
    (hx : NodeEnd n cm args x) (hsplit : splitMod (Binary.coreModule cm) = true)
    (hfun : (Binary.coreModule cm).imports.all
      (fun i => match i.type with | .func _ => true | _ => false) = true) :
    ∃ O : Own, OwnOk O x.store ∧ ∀ a, a < x.store.funcs.length → O.fn a := by
  obtain ⟨-, hp, ys, -, hstart⟩ := hx
  obtain ⟨mtI, f', st₀, -, -, hi, -, hst₀⟩ :=
    Silmaril.Wasm.Component.Engine.Core3.Typed.prepareE?_inv hp
  have hi' : instantiateOnce? (irStore (CoreModule.imports cm).length)
      { Binary.coreModule cm with start := none }
      (Silmaril.Wasm.Link.GC.Preparation.imports (List.range (CoreModule.imports cm).length)) =
      some (x.inst.store, f', none) := by
    rw [instantiateOnce?_noStart,
      show Silmaril.Wasm.Link.GC.Preparation.imports (List.range (CoreModule.imports cm).length) =
        (List.range (CoreModule.imports cm).length).map ExternAddr.func from rfl, hi]
    rfl
  have hprof : Silmaril.Wasm.Link.GC.inProfile { Binary.coreModule cm with start := none } = true := by
    simp only [splitMod, Bool.and_eq_true, List.isEmpty_iff] at hsplit
    simp [Silmaril.Wasm.Link.GC.inProfile, hsplit.1.1.1.1, hsplit.1.1.1.2, hsplit.1.1.2,
      hsplit.1.2, hsplit.2]
    exact List.all_eq_true.mp hfun
  obtain ⟨hgood, hmodg⟩ := storeGood_once hprof hi'
    (fun fi hfi c hc => by
      simp only [irStore, List.mem_map, List.mem_range] at hfi
      obtain ⟨i, -, rfl⟩ := hfi
      cases hc)
    rfl rfl rfl (fun a ha => by simpa [irStore] using ha)
  rcases hstart with ⟨-, -, hxs⟩ | ⟨f, c', vs, hfs, hrun, -, hxs⟩
  · rw [hxs]
    exact ⟨ownOf x.inst.store, ownOk_of_partRel hgood.partRel, fun a ha => ha⟩
  · obtain ⟨y, -, hy⟩ := hst₀ f hfs
    have hfa : (show Nat from f) < x.inst.store.funcs.length := hmodg.funcs f (List.mem_of_getElem? hy)
    have h₀ : RunInv ((Silmaril.Wasm.SingleThreaded.Thread.invoke f []).config x.inst.store) :=
      ⟨Ren.id, ownOf x.inst.store, x.inst.store, hgood.partRel, (invoke_good hfa (fun _ h => by cases h)).1,
        (invoke_good hfa (fun _ h => by cases h)).2, fun a ha => ha⟩
    obtain ⟨ρ, O, σ, hR, -, -, hfn⟩ := startRun_inv hrun h₀
    have e : (c'.2.config c'.1).store = x.store := by
      rw [hxs]; exact Silmaril.Wasm.SingleThreaded.Thread.config_store _ _
    rw [e] at hR hfn
    exact ⟨O, ownOk_of_partRel hR, hfn⟩

theorem nodeSplit_all : ∀ {ps : List (Binary.CoreMod × List Impl)}
    {qs : List (Silmaril.Wasm.Module × List Impl)},
    List.Forall₂ NodeW (coreNodes ps) qs →
    (qs.all fun p => splitMod p.1 &&
      p.1.imports.all (fun i => match i.type with | .func _ => true | _ => false)) = true →
    ∀ p ∈ ps, splitMod (Binary.coreModule p.1) = true ∧ (Binary.coreModule p.1).imports.all
      (fun i => match i.type with | .func _ => true | _ => false) = true
  | [], _, _, _ => fun _ h => by cases h
  | p :: ps, q :: qs, .cons hW hF, hall => by
    simp only [List.all_cons, Bool.and_eq_true] at hall
    intro p' hp'
    rcases List.mem_cons.mp hp' with rfl | hp'
    · obtain ⟨cm, he, hd, -⟩ := hW
      injection he with he₁ he₂
      subst he₁
      have hmod : Binary.coreModule p'.1 = q.1 := by
        unfold Binary.coreModule
        rw [hd]
        rfl
      rw [hmod]
      exact hall.1
    · exact nodeSplit_all hF hall.2 p' hp'

/-- **In the fragment, every node's module is in the split fragment and imports only functions.** -/
theorem nodeSplit_frag {b : ByteArray} {c : Comp Binary.CoreMod} {r : Conformance.RefComponent}
    {ps : List (Binary.CoreMod × List Impl)} (hc : Binary.parseComponent b = .ok c)
    (hr : Conformance.decodeRef b = .ok r) (hf : MultiImpFrag r) (hn : c.nodes = coreNodes ps) :
    ∀ p ∈ ps, splitMod (Binary.coreModule p.1) = true ∧ (Binary.coreModule p.1).imports.all
      (fun i => match i.type with | .func _ => true | _ => false) = true := by
  obtain ⟨-, hw, -, -⟩ := multiImpFrag_inv hf
  obtain ⟨R, hR, hsn⟩ := multiImpFrag_split hf
  obtain ⟨R', hR', -, -, hN⟩ := relW_of_decode hc hr (inFrag_of_hostWired hw)
  rw [hR] at hR'
  cases hR'
  rw [hn] at hN
  exact nodeSplit_all hN hsn

end Node

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi
