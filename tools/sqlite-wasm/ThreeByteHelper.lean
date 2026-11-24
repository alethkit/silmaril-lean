module

public import SqliteWasm.ThreeByteLoopMemory
import Silmaril.Wasm.Auto2.VCGen.Thms
import Silmaril.Wasm.Verify.Kernel.Defs

@[expose] public section

namespace SqliteWasm.ThreeByte.Symbolic

open Silmaril.Wasm Silmaril.Wasm.Auto2.VCGen
open Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open SqliteWasmArtifact

set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

/-- The actual linked helper body at function index 547. -/
def quotedHelper : Func := (definedFunction? sqlite 547).get (by decide +kernel)

private def assumptions (_ : Nat) (original : ByteArray) : List (BitVec 32) → Prop
  | [ptr, sp] => Buffers original ptr sp
  | _ => False

private def relations (tag : Nat) (original mem : ByteArray) : List (BitVec 32) → Prop
  | [sp, x, idx, remaining] =>
    tag = 0 ∧ idx.toNat < 3 ∧ remaining.toNat = x.toNat / 128 ^ idx.toNat ∧
      mem = digitsMemory original sp.toNat x.toNat idx.toNat
  | [ptr, sp, x, idx, src] =>
    tag = 1 ∧ idx.toNat < 3 ∧ src.toNat = scratchAddress sp + 2 - idx.toNat ∧
      mem = copyMemory original ptr sp x idx.toNat
  | [ptr, sp, x] =>
    tag = 2 ∧ mem = outputBytes original ptr sp (radixValue x)
  | _ => False

private def model : Fns := { pr := assumptions, pr2 := relations }

private def symPre : Fm :=
  .and (.rel (.le .unsigned) (.lit .i64 16384) (.var .i64 1))
    (.and (.rel (.lt .unsigned) (.var .i64 1) (.lit .i64 2097152))
      (.pr 0 (.v 0) [.var .i32 0, .var .i32 2]))

private def digitInvariant : Fm :=
  .and (.rel (.lt .unsigned) (.loc .i64 1) (.lit .i64 4294967296))
    (.pr2 0 (.v 0) .cur
      [.var .i32 2, .wrap (.var .i64 1), .loc .i32 3, .wrap (.loc .i64 1)])

private def copyInvariant : Fm :=
  .and (.rel .eq (.loc .i32 3) (.lit .i32 3))
    (.pr2 1 (.v 0) .cur
      [.var .i32 0, .var .i32 2, .wrap (.var .i64 1), .loc .i32 2, .loc .i32 4])

private def symPost : Fm :=
  .and (.rel .eq (.loc .i32 0) (.lit .i32 3))
    (.and (.rel .eq (.loc .i32 1) (.var .i32 2))
      (.pr2 2 (.v 0) .cur [.var .i32 0, .var .i32 2, .wrap (.var .i64 1)]))

private def spec : FnSpec where
  params := [.i32, .i64]
  results := [.i32]
  globals := [.i32]
  mem := true
  total := true
  pre := symPre
  post := symPost
  inv := [digitInvariant, copyInvariant, .not .tt]
  var := [
    .bin .sub (.lit .i32 3) (.loc .i32 3),
    .bin .sub (.lit .i32 3) (.loc .i32 2),
    .bin .add (.loc .i32 3) (.lit .i32 1)]

private def generated : List Fm := genFunc spec quotedHelper 128

private theorem countDown (j : BitVec 32) (index : j.toNat < 3) :
    (3#32 - (j + 1#32)).toNat < (3#32 - j).toNat := by
  have next := countNext j index
  rw [BitVec.toNat_sub_of_le (show (j + 1#32).toNat ≤ (3#32).toNat by
    change (j + 1#32).toNat ≤ 3; omega)]
  rw [BitVec.toNat_sub_of_le (show j.toNat ≤ (3#32).toNat by
    change j.toNat ≤ 3; omega)]
  change 3 - (j + 1#32).toNat < 3 - j.toNat
  omega

private theorem outputAddress (B : ByteArray) (ptr sp j : BitVec 32)
    (buffers : Buffers B ptr sp) (index : j.toNat < 3) :
    (ptr + j).toNat = ptr.toNat + j.toNat := by
  apply BitVec.toNat_add_of_lt
  have bound := buffers.outputNoWrap
  omega

private theorem valid : AllValid model generated := by
  vcgen4_reduce
  vcgen4_den
  simp only [IntType.width, model, relations, assumptions, true_and]
  and_intros
  all_goals vcgen4_vars
  all_goals intro h
  all_goals repeat' cases_type And
  all_goals subst_vars
  all_goals try simp only [not_not, Nat.add_zero, BitVec.toNat_ofNat, Nat.zero_mod,
    show 127 % (2 ^ 64 : Nat) = 127 from rfl] at *
  all_goals try omega
  all_goals have buffers : Buffers M0 v0 v2 := by assumption
  all_goals have stack := buffers.stackSubtraction
  all_goals have scratchBound := buffers.scratchInBounds
  all_goals have vNat := wrapNat w1 (by omega)
  all_goals have lo : 16384 ≤ (w1.setWidth 32).toNat := by rw [vNat]; omega
  all_goals have hi : (w1.setWidth 32).toNat < 2097152 := by rw [vNat]; omega
  · refine ⟨by omega, by decide, by simp, ?_⟩
    exact (digitsMemory_zero M0 v2.toNat (w1.setWidth 32).toNat).symm
  · have idx : v8.toNat < 3 := by assumption
    rw [noWrapScratch v2 v8 stack (by omega), digitsMemorySize (bound := by
      change scratchAddress v2 + v8.toNat ≤ M0.size; omega)]
    omega
  · have idx : v8.toNat < 3 := by assumption
    have rem : w6.toNat = w1.toNat / 128 ^ v8.toNat := by
      rwa [← wrapNat w6 (by omega), ← vNat]
    have go := (digitBranch w1 _ w6 (by omega) (by omega) idx rem).1.mp
      (show (if 127 < w6.toNat then (1 : BitVec 32) else 0) ≠ 0 by assumption)
    have sh := remainingShift w1 _ w6 rem
    have shifted : (w6 >>> 7).toNat < 4294967296 := by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      omega
    refine ⟨shifted, by rw [countNext v8 idx]; omega, ?_, ?_⟩
    · rw [wrapNat _ shifted, vNat, countNext v8 idx, sh]
    · rw [countNext v8 idx, noWrapScratch v2 v8 stack (by omega)]
      exact digitIteration _ _ _ _ _ (rem.trans (by rw [vNat])) (by omega)
  · exact countDown v8 (by assumption)
  · rw [storeSize, digitsMemorySize (bound := by
      change scratchAddress v2 + v8.toNat ≤ M0.size; omega)]
    have base := scratchBase v2 stack
    omega
  · rw [storeSize, digitsMemorySize (bound := by
      change scratchAddress v2 + v8.toNat ≤ M0.size; omega)]
    have base := scratchBase v2 stack
    omega
  · have idx : v8.toNat < 3 := by assumption
    have rem : w6.toNat = w1.toNat / 128 ^ v8.toNat := by
      rwa [← wrapNat w6 (by omega), ← vNat]
    have done := (digitBranch w1 _ w6 (by omega) (by omega) idx rem).2.mp
      (show (if 127 < w6.toNat then (1 : BitVec 32) else 0) = 0 by assumption)
    have three : v8 + 1#32 = 3#32 := by
      apply BitVec.eq_of_toNat_eq
      rw [countNext v8 idx]
      change v8.toNat + 1 = 3
      omega
    rw [three]
    refine ⟨rfl, by decide, ?_, ?_⟩
    · rw [show v2 - 16#32 + 6#32 + 3#32 + 4294967295#32 =
        v2 - 16#32 + 6#32 + 2#32 by rw [BitVec.add_assoc]; rfl,
        noWrapScratch v2 2#32 stack (by decide)]
      rfl
    · rw [scratchBase _ stack, noWrapScratch v2 v8 stack (by omega),
        digitIteration _ _ _ _ _ (rem.trans (by rw [vNat])) (by omega),
        show v8.toNat + 1 = 3 by omega, copyZero]
      exact clearDigit _ _ _ _ buffers lo hi
  · rw [copyMemorySize _ _ _ _ _ buffers lo hi]
    omega
  · rw [copyMemorySize _ _ _ _ _ buffers lo hi, outputAddress _ _ _ _ buffers (by assumption)]
    have := buffers.outputInBounds
    omega
  · have idx : v20.toNat < 3 := by assumption
    have next := countNext v20 idx
    have more : (v20 + 1#32).toNat < 3 := by
      have neq : 3#32 ≠ v20 + 1#32 := by assumption
      have differs : (v20 + 1#32).toNat ≠ 3 := fun same => neq (BitVec.eq_of_toNat_eq same.symm)
      omega
    have src : v22.toNat = scratchAddress v2 + 2 - v20.toNat := by assumption
    have positive : 1 ≤ v22.toNat := by unfold scratchAddress at src; omega
    have prev : (v22 + 4294967295#32).toNat = v22.toNat - 1 := by
      rw [show v22 + 4294967295#32 = v22 - 1 from (BitVec.sub_eq_add_neg v22 1#32).symm,
        BitVec.toNat_sub_of_le (by exact positive)]
      rfl
    refine ⟨True.intro, more, by rw [prev, next, src]; omega, ?_⟩
    rw [next, outputAddress _ _ _ _ buffers idx, src]
    exact copyIteration _ _ _ _ _ idx buffers lo hi
  · exact countDown v20 (by assumption)
  · have idx : v20.toNat < 3 := by assumption
    have last : 3#32 = v20 + 1#32 := by assumption
    have count : v20.toNat + 1 = 3 := by
      rw [← countNext v20 idx, ← last]
      rfl
    have src : v22.toNat = scratchAddress v2 + 2 - v20.toNat := by assumption
    refine ⟨True.intro, ?_⟩
    rw [outputAddress _ _ _ _ buffers idx, src, copyIteration _ _ _ _ _ idx buffers lo hi,
      count, copyDone _ _ _ _ lo hi]

#print axioms valid

open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Post)
open Silmaril.Wasm.Validation (CGlobalType Expand Ty)

private theorem reachExit {H : Type} {P : Numerics.Profile} {host : HostSemantics H}
    {Q : Post H} {start : Config H} (safe : TSafe P host Q start) :
    ∃ final outcome, Steps P host start final ∧ Exits outcome final.code ∧
      Q final.store final.frame outcome := by
  induction safe with
  | exit outcome exits post => exact ⟨_, outcome, .refl, exits, post⟩
  | step progress _ ih =>
    obtain ⟨next, step⟩ := progress
    obtain ⟨final, outcome, steps, exits, post⟩ := ih next step
    exact ⟨final, outcome, step.steps.trans steps, exits, post⟩

private theorem singleI32 (values : List Val) (typed : values.map valTy = [some .i32]) :
    ∃ word : BitVec 32, values = [.i32 word] := by
  cases values with
  | nil => simp at typed
  | cons head tail =>
    have length : tail.length = 0 := by
      have lengths := congrArg List.length typed
      simpa using lengths
    have empty := List.length_eq_zero_iff.mp length
    subst tail
    cases head with
    | num n =>
      rcases n with ⟨t, word⟩
      cases t with
      | int t =>
        cases t with
        | i32 => exact ⟨word, rfl⟩
        | i64 => simp [valTy] at typed
      | float t => simp [valTy] at typed
    | vec _ => simp [valTy] at typed
    | ref _ => simp [valTy] at typed

private theorem originalValue (value : UInt64) (upper : value.toNat < 2097152) :
    radixValue (value.toBitVec.setWidth 32) = value := by
  apply UInt64.toNat_inj.mp
  rw [toNat_radixValue, wrapNat _ (by rw [UInt64.toNat_toBitVec]; omega),
    UInt64.toNat_toBitVec]

private theorem helperRun {H : Type} {P : Numerics.Profile} {host : HostSemantics H}
    (s : Store H) (caller : Frame) (callee : ModuleInst) (ptr sp : BitVec 32) (value : UInt64)
    (address globalAddress : Nat) (mem : MemInst) (globalType : CGlobalType)
    (lower : 16384 ≤ value.toNat) (upper : value.toNat < 2097152)
    (memLink : callee.mems[0]? = some address) (memEntry : s.mems[address]? = some mem)
    (globLink : callee.globals[0]? = some globalAddress)
    (globEntry : s.globals[globalAddress]? = some ⟨globalType, .i32 sp⟩)
    (buffers : Buffers mem.bytes ptr sp) :
    Steps P host ⟨s, caller, [activation callee quotedHelper ptr value]⟩
      ⟨postStore s address mem ptr sp value, caller, [constI32 3]⟩ := by
  let ρ : Env := ⟨(fun i => if i = 0 then ptr else sp), (fun _ => value.toBitVec), fun _ => mem.bytes⟩
  let fi : FuncInst H := ⟨default, callee, .wasm quotedHelper⟩
  have hm : MemOk spec s callee (ρ.mem 0) := ⟨address, mem, memLink, memEntry, rfl⟩
  have hg : GlobOk spec s callee ρ := by
    constructor
    · intro g g' a lt lt' _ _
      change g < 1 at lt
      change g' < 1 at lt'
      omega
    · intro g t lookup
      change ([.i32] : List IntType)[g]? = some t at lookup
      cases g with
      | zero =>
        obtain rfl : IntType.i32 = t := Option.some.inj lookup
        exact ⟨globalAddress, _, globLink, globEntry, rfl⟩
      | succ g => simp at lookup
  have hp : spec.preF.den model ρ ρ := by
    change 16384 ≤ value.toBitVec.toNat ∧ value.toBitVec.toNat < 2097152 ∧ Buffers mem.bytes ptr sp
    rw [UInt64.toNat_toBitVec]
    exact ⟨lower, upper, buffers⟩
  have wellScoped : spec.wellScoped = true := by kernel_rfl
  have locals : Silmaril.Wasm.Auto.VCGen.intTys? quotedHelper.locals = some [.i32, .i32, .i32] := by kernel_rfl
  have vc : AllValid model
      (gen spec (spec.params ++ [.i32, .i32, .i32] ++ spec.globals) 128 []
        (endVC spec (spec.params ++ [.i32, .i32, .i32] ++ spec.globals)) 0
        quotedHelper.body (initSt spec [.i32, .i32, .i32])) := valid
  have body := body_wp (c := .total) (fi := fi) (P := P) (host := host) locals wellScoped
    (fun _ => rfl) vc (s := s) (ρ₀ := ρ) (by simp [CallsOK, spec]) hm hg hp
  let post := callPost caller [] ((fspec model spec 0 fi).post s (argsOf spec ρ))
  have bodySafe : TSafe P host (bodyPostT P host 1 caller [] post)
      ⟨s, callFrame callee quotedHelper ptr value,
        expression quotedHelper.body⟩ := by
    refine TSafe.post_mono body ?_
    intro s' f' o ho
    exact bodyPostT_of_postOf (fi := fi) (a := 0) wellScoped rfl rfl hm hg
      (drop_lt_init [.i32, .i32, .i32]) ho
  have packed : TSafe P host post
      ⟨s, caller, [activation callee quotedHelper ptr value]⟩ :=
    TSafe.frame (TSafe.label bodySafe)
  obtain ⟨⟨s', f', code⟩, outcome, steps, exits, result⟩ := reachExit packed
  obtain ⟨rfl, normal | trapped | thrown⟩ := result
  · obtain ⟨values, rfl, returned⟩ := normal
    obtain ⟨B, G, store, globalTypes, res, same, _, resultTypes, facts⟩ := returned
    cases same
    obtain ⟨word, rfl⟩ := singleI32 values resultTypes
    obtain ⟨sp', rfl⟩ := singleI32 G globalTypes
    have final := facts ρ rfl hm hg
    change word = 3#32 ∧ sp' = sp ∧ 2 = 2 ∧
      B = outputBytes mem.bytes ptr sp (radixValue (value.toBitVec.setWidth 32)) at final
    obtain ⟨resultWord, stackWord, _, finalBytes⟩ := final
    subst word sp' B
    rw [originalValue value upper] at store
    have unchanged : setGs (upd spec s callee (outputBytes mem.bytes ptr sp value)) callee
        [.i32 sp] = upd spec s callee (outputBytes mem.bytes ptr sp value) := by
      apply setGs_self
      intro i bound
      have eq : i = 0 := by change i < 1 at bound; omega
      subst i
      refine ⟨globalAddress, ⟨globalType, .i32 sp⟩, globLink, ?_, rfl⟩
      change (setM s callee _).globals[globalAddress]? = _
      rw [setM_some memLink memEntry]
      exact globEntry
    rw [unchanged] at store
    change s' = setM s callee (outputBytes mem.bytes ptr sp value) at store
    rw [setM_some memLink memEntry] at store
    change code = [constI32 3] at exits
    subst s' code
    exact steps
  · obtain ⟨_, _, _, _, _, _, impossible, _⟩ := trapped
    cases impossible
  · obtain ⟨_, _, _, _, _, _, _, impossible, _⟩ := thrown
    cases impossible

/-- The quoted helper terminates with the exact scratch and output image for every
width-three input and every store satisfying the disjoint-buffer contract. -/
theorem quotedHelper_threeByte {H : Type} (P : Numerics.Profile) (host : HostSemantics H)
    (callee : ModuleInst) : HelperContract P host quotedHelper callee := by
  intro s caller ptr sp value address globalAddress mem globalType lo hi mapped global buffers
  unfold Store.mem? at mapped
  obtain ⟨ma, memLink, rest⟩ := Option.bind_eq_some_iff.mp mapped
  obtain ⟨mi, memEntry, pair⟩ := Option.bind_eq_some_iff.mp rest
  rcases Prod.mk.inj (Option.some.inj pair) with ⟨rfl, rfl⟩
  unfold Store.global? at global
  obtain ⟨ga, globLink, rest⟩ := Option.bind_eq_some_iff.mp global
  obtain ⟨gi, globEntry, pair⟩ := Option.bind_eq_some_iff.mp rest
  rcases Prod.mk.inj (Option.some.inj pair) with ⟨rfl, rfl⟩
  exact ⟨by kernel_rfl,
    helperRun s caller callee ptr sp value _ _ _ globalType lo hi
      memLink memEntry globLink globEntry buffers⟩

/-- A call through the reactor's wrapper writes the three-byte Lean varint and its
scratch image for the whole width-three interval. -/
theorem putVarint_threeByte {H : Type} {P : Numerics.Profile} {host : HostSemantics H}
    {s : Store H} {caller : Frame} {putFn : Func} {putAddress helperAddress : Nat}
    {putInstance helperInstance : FuncInst H} {ptr sp : BitVec 32} {value : UInt64}
    {address globalAddress : Nat} {mem : MemInst} {globalType : CGlobalType}
    (selected : definedFunction? sqlite 530 = some putFn)
    (putBinding : s.func? caller ⟨530⟩ = some (putAddress, putInstance))
    (helperBinding : s.func? (callFrame putInstance.module putFn ptr value) ⟨547⟩ =
      some (helperAddress, helperInstance))
    (putCode : putInstance.code = .wasm putFn)
    (helperCode : helperInstance.code = .wasm quotedHelper)
    (putType : Expand putInstance.type (.func (.cons Ty.i32 (.cons Ty.i64 .nil)) (.cons Ty.i32 .nil)))
    (helperType : Expand helperInstance.type (.func (.cons Ty.i32 (.cons Ty.i64 .nil)) (.cons Ty.i32 .nil)))
    (lower : 16384 ≤ value.toNat) (upper : value.toNat < 2097152)
    (mapped : s.mem? (callFrame helperInstance.module quotedHelper ptr value) ⟨0⟩ =
      some (address, mem))
    (global : s.global? (callFrame helperInstance.module quotedHelper ptr value) ⟨0⟩ =
      some (globalAddress, ⟨globalType, .i32 sp⟩))
    (buffers : Buffers mem.bytes ptr sp) :
    Steps P host ⟨s, caller, vals (args ptr value) ++ [.plain (.call ⟨530⟩)]⟩
      ⟨postStore s address mem ptr sp value, caller, [constI32 3]⟩ :=
  putVarint_threeByte_of_helper selected putBinding helperBinding putCode helperCode putType helperType
    lower (quotedHelper_threeByte P host helperInstance.module s
      (callFrame putInstance.module putFn ptr value) ptr sp value address globalAddress mem
      globalType lower upper mapped global buffers)

#print axioms quotedHelper_threeByte
#print axioms putVarint_threeByte

end SqliteWasm.ThreeByte.Symbolic
