module

public import SqliteWasm.OrdinaryVarintMemory
public import SqliteWasm.ThreeByteHelper
import Silmaril.Wasm.Auto2.VCGen.Thms
import Silmaril.Wasm.Verify.Kernel.Defs

@[expose] public section

namespace SqliteWasm.OrdinaryVarint

open Silmaril.Wasm Silmaril.Wasm.Auto2.VCGen
open Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open SqliteWasmArtifact
open ThreeByte (scratchAddress scratchAddress_eq outputBytes postStore callFrame activation args putVarint_forward)
open ThreeByte.Symbolic (quotedHelper digitsMemory digitsMemory_zero digitsMemorySize
  scratchBase digitIteration remainingShift storeSize reachExit singleI32)

set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

def joinHalves (lo hi : BitVec 32) : Nat := hi.toNat * 2 ^ 32 + lo.toNat

theorem joinSplit (x : BitVec 64) :
    joinHalves (x.setWidth 32) ((x >>> 32).setWidth 32) = x.toNat := by
  simp only [joinHalves, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have bound := x.isLt
  have high : x.toNat / 2 ^ 32 < 2 ^ 32 := by omega
  rw [Nat.mod_eq_of_lt high, Nat.mul_comm]
  exact Nat.div_add_mod _ _

theorem u64OfNat (x : BitVec 64) : (UInt64.ofNat x.toNat).toNat = x.toNat := by
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by exact x.isLt)]

private def assumptions (width _ : Nat) (original : ByteArray) : List (BitVec 32) → Prop
  | [ptr, sp, lo, hi] => Width (joinHalves lo hi) width ∧ Buffers original ptr sp width
  | _ => False

private def relations (width : Nat) (tag : Nat) (original mem : ByteArray) (args : List (BitVec 32)) : Prop :=
  match tag, args with
  | 0, [sp, idx, lo, hi, leftLo, leftHi] =>
    idx.toNat < width ∧ joinHalves leftLo leftHi = joinHalves lo hi / 128 ^ idx.toNat ∧
    mem = digitsMemory original sp.toNat (joinHalves lo hi) idx.toNat
  | 1, [ptr, sp, idx, src, lo, hi] =>
    idx.toNat < width ∧ src.toNat = scratchAddress sp + (width - 1) - idx.toNat ∧
    mem = copyMemory original ptr sp (UInt64.ofNat (joinHalves lo hi)) idx.toNat
  | 2, [ptr, sp, lo, hi] =>
    mem = outputBytes original ptr sp (UInt64.ofNat (joinHalves lo hi))
  | _, _ => False

private def model (width : Nat) : Fns :=
  { pr := assumptions width, pr2 := relations width, f32 := fun _ _ => BitVec.ofNat 32 width }

/-- The closed generator input refers to the proof's width through a specification
function. The same generated conditions apply to every width admitted by the precondition. -/
private def widthTerm : Tm .i32 := .fn 0 (.lit .i32 0)

def splitWord (x : Tm .i64) : List (Tm .i32) :=
  [.wrap x, .wrap (.bin (.shr .unsigned) x (.lit .i64 32))]

private def initialValue : List (Tm .i32) := splitWord (.var .i64 1)

private def symPre : Fm := .pr 0 (.v 0) ([.var .i32 0, .var .i32 2] ++ initialValue)

private def digitInvariant : Fm :=
  .pr2 0 (.v 0) .cur ([.var .i32 2, .loc .i32 3] ++ initialValue ++ splitWord (.loc .i64 1))

private def copyInvariant : Fm :=
  .and (.rel .eq (.loc .i32 3) widthTerm)
    (.pr2 1 (.v 0) .cur
      ([.var .i32 0, .var .i32 2, .loc .i32 2, .loc .i32 4] ++ initialValue))

private def symPost : Fm :=
  .and (.rel .eq (.loc .i32 0) widthTerm)
    (.and (.rel .eq (.loc .i32 1) (.var .i32 2))
      (.pr2 2 (.v 0) .cur ([.var .i32 0, .var .i32 2] ++ initialValue)))

/-- The signature, memory and global used by both branches of the quoted helper. -/
def helperSpec (pre post : Fm) (invariants : List Fm) (variants : List (Tm .i32)) : FnSpec where
  params := [.i32, .i64]
  results := [.i32]
  globals := [.i32]
  mem := true
  total := true
  pre := pre
  post := post
  inv := invariants
  var := variants

private def spec : FnSpec :=
  helperSpec symPre symPost [digitInvariant, copyInvariant, .not .tt]
    [.bin .sub widthTerm (.loc .i32 3), .bin .sub widthTerm (.loc .i32 2),
      .bin .add (.loc .i32 3) (.lit .i32 1)]

private def generated : List Fm := genFunc spec quotedHelper 128

private theorem excludeNine {x width : Nat} (fits : Width x width)
    (nine : 72057594037927935 < x) : False := by
  have bound : x < 72057594037927936 := fits.belowNine
  omega

private theorem continue_iff {x width j : Nat} (fits : Width x width) :
    127 < x / 128 ^ j ↔ j + 1 < width := by
  change 128 ≤ x / 128 ^ j ↔ _
  rw [Nat.le_div_iff_mul_le (Nat.pow_pos (by decide)), ← Nat.pow_succ']
  constructor
  · intro wrote
    by_contra! order
    have mono : 128 ^ width ≤ 128 ^ (j + 1) := Nat.pow_le_pow_right (by decide) order
    exact (Nat.not_le_of_lt fits.upper) (mono.trans wrote)
  · intro order
    exact (Nat.pow_le_pow_right (by decide) (show j + 1 ≤ width - 1 by omega)).trans fits.lower

private theorem digitTest {x width j : Nat} {w : BitVec 64} (fits : Width x width)
    (rem : w.toNat = x / 128 ^ j) :
    ((if 127 < w.toNat then (1 : BitVec 32) else 0) ≠ 0 ↔ j + 1 < width) := by
  rw [rem]
  split <;> simp_all [continue_iff fits]

private theorem widthWord (width : Nat) (bound : width ≤ 8) :
    (BitVec.ofNat 32 width).toNat = width := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

private theorem countNext (j : BitVec 32) (index : j.toNat < 8) :
    (j + 1#32).toNat = j.toNat + 1 :=
  BitVec.toNat_add_of_lt (by change j.toNat + 1 < 2 ^ 32; omega)

private theorem countDown (width : Nat) (j : BitVec 32) (index : j.toNat < width) (bound : width ≤ 8) :
    (BitVec.ofNat 32 width - (j + 1#32)).toNat < (BitVec.ofNat 32 width - j).toNat := by
  have next := countNext j (by omega)
  have w := widthWord width bound
  have nextBound : (j + 1#32).toNat ≤ (BitVec.ofNat 32 width).toNat := by omega
  have indexBound : j.toNat ≤ (BitVec.ofNat 32 width).toNat := by omega
  rw [BitVec.toNat_sub_of_le nextBound, BitVec.toNat_sub_of_le indexBound, w, next]
  omega

private theorem noWrapScratch (sp idx : BitVec 32) (stack : 16 ≤ sp.toNat)
    (index : idx.toNat ≤ 8) :
    (sp - 16#32 + 6#32 + idx).toNat = scratchAddress sp + idx.toNat := by
  have base : (sp - 16#32 + 6#32).toNat = scratchAddress sp := scratchAddress_eq sp stack
  have ceiling := sp.isLt
  rw [BitVec.toNat_add_of_lt (by rw [base, scratchAddress]; omega), base]

private theorem outputAddress (B : ByteArray) (ptr sp j : BitVec 32) (width : Nat)
    (buffers : Buffers B ptr sp width) (index : j.toNat < width) :
    (ptr + j).toNat = ptr.toNat + j.toNat := by
  apply BitVec.toNat_add_of_lt
  have bound := buffers.outputNoWrap
  omega

private theorem valid (width : Nat) : AllValid (model width) generated := by
  vcgen4_reduce
  vcgen4_den
  simp only [IntType.width, model, relations, assumptions, joinSplit]
  and_intros
  all_goals vcgen4_vars
  all_goals intro h
  all_goals repeat' cases_type And
  all_goals subst_vars
  all_goals try simp only [not_not, Nat.add_zero, BitVec.toNat_ofNat, Nat.zero_mod,
    show 127 % (2 ^ 64 : Nat) = 127 from rfl] at *
  all_goals have fits : Width w1.toNat width := by assumption
  all_goals try exact (excludeNine fits (by assumption)).elim
  all_goals have buffers : Buffers M0 v0 v2 width := by assumption
  all_goals have stack := buffers.stackSubtraction
  all_goals have scratchBound := buffers.scratchInBounds
  all_goals have positive := fits.positive
  all_goals have widthBound := fits.ordinary
  all_goals have valueFits : Width (UInt64.ofNat w1.toNat).toNat width := by rwa [u64OfNat]
  · refine ⟨positive, by simp, ?_⟩
    exact (digitsMemory_zero M0 v2.toNat w1.toNat).symm
  · have idx : v8.toNat < width := by assumption
    rw [noWrapScratch v2 v8 stack (by omega), digitsMemorySize (bound := by
      change scratchAddress v2 + v8.toNat ≤ M0.size; omega)]
    omega
  · have idx : v8.toNat < width := by assumption
    have rem : w6.toNat = w1.toNat / 128 ^ v8.toNat := by assumption
    have go := (digitTest fits rem).mp
      (show (if 127 < w6.toNat then (1 : BitVec 32) else 0) ≠ 0 by assumption)
    rw [countNext v8 (by omega)]
    refine ⟨go, remainingShift w1 _ w6 rem, ?_⟩
    rw [noWrapScratch v2 v8 stack (by omega)]
    exact digitIteration _ _ _ _ _ rem (by omega)
  · exact countDown width v8 (by assumption) widthBound
  · rw [storeSize, digitsMemorySize (bound := by
      change scratchAddress v2 + v8.toNat ≤ M0.size; omega)]
    have base := scratchBase v2 stack
    omega
  · rw [storeSize, digitsMemorySize (bound := by
      change scratchAddress v2 + v8.toNat ≤ M0.size; omega)]
    have base := scratchBase v2 stack
    omega
  · have idx : v8.toNat < width := by assumption
    have rem : w6.toNat = w1.toNat / 128 ^ v8.toNat := by assumption
    have stop : ¬ v8.toNat + 1 < width := by
      intro cont
      exact (digitTest fits rem).mpr cont (by assumption)
    have count : v8.toNat + 1 = width := by omega
    have wordCount : v8 + 1#32 = BitVec.ofNat 32 width := by
      apply BitVec.eq_of_toNat_eq
      rw [countNext v8 (by omega), widthWord _ widthBound, count]
    refine ⟨wordCount, positive, ?_, ?_⟩
    · rw [show v2 - 16#32 + 6#32 + (v8 + 1#32) + 4294967295#32 =
        v2 - 16#32 + 6#32 + v8 by
          rw [BitVec.add_assoc (v2 - 16#32 + 6#32),
            BitVec.add_assoc v8 (1#32)]
          change _ + (v8 + 0#32) = _
          simp, noWrapScratch v2 v8 stack (by omega)]
      omega
    · rw [scratchBase _ stack, noWrapScratch v2 v8 stack (by omega),
        digitIteration _ _ _ _ _ rem (by omega), count, copyZero]
      simpa only [u64OfNat] using
        clearDigit M0 v0 v2 (UInt64.ofNat w1.toNat) width buffers valueFits
  · rw [copyMemorySize _ _ _ _ _ _ buffers valueFits]
    omega
  · rw [copyMemorySize _ _ _ _ _ _ buffers valueFits,
      outputAddress _ _ _ _ _ buffers (by assumption)]
    have := buffers.outputInBounds
    omega
  · have idx : v20.toNat < width := by assumption
    have next := countNext v20 (by omega)
    have more : (v20 + 1#32).toNat < width := by
      have neq : BitVec.ofNat 32 width ≠ v20 + 1#32 := by assumption
      have differs : (v20 + 1#32).toNat ≠ width := fun same =>
        neq (BitVec.eq_of_toNat_eq ((widthWord width widthBound).trans same.symm))
      omega
    have src : v22.toNat = scratchAddress v2 + (width - 1) - v20.toNat := by assumption
    have srcPositive : 1 ≤ v22.toNat := by unfold scratchAddress at src; omega
    have prev : (v22 + 4294967295#32).toNat = v22.toNat - 1 := by
      rw [show v22 + 4294967295#32 = v22 - 1 from (BitVec.sub_eq_add_neg v22 1#32).symm,
        BitVec.toNat_sub_of_le (by exact srcPositive)]
      rfl
    refine ⟨True.intro, more, by rw [prev, next, src]; omega, ?_⟩
    rw [next, outputAddress _ _ _ _ _ buffers idx, src]
    exact copyIteration _ _ _ _ _ _ buffers valueFits idx
  · exact countDown width v20 (by assumption) widthBound
  · have idx : v20.toNat < width := by assumption
    have last : BitVec.ofNat 32 width = v20 + 1#32 := by assumption
    have count : v20.toNat + 1 = width := by
      rw [← countNext v20 (by omega), ← last, widthWord _ widthBound]
    have src : v22.toNat = scratchAddress v2 + (width - 1) - v20.toNat := by assumption
    refine ⟨True.intro, ?_⟩
    rw [outputAddress _ _ _ _ _ buffers idx, src, copyIteration _ _ _ _ _ _ buffers valueFits idx,
      count, copyDone _ _ _ _ _ valueFits]

#print axioms valid

open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Validation (CGlobalType Expand Ty)

def helperEnv (ptr sp : BitVec 32) (value : UInt64) (bytes : ByteArray) : Env :=
  ⟨(fun i => if i = 0 then ptr else sp), (fun _ => value.toBitVec), fun _ => bytes⟩

/-- Transfer validated path conditions for the actual helper body to an exact Core exit. -/
theorem helperSteps_of_vcs {H : Type} {P : Numerics.Profile} {host : HostSemantics H}
    (F : Fns) (pre post : Fm) (invariants : List Fm) (variants : List (Tm .i32))
    (wellScoped : (helperSpec pre post invariants variants).wellScoped = true)
    (validConditions : AllValid F (genFunc (helperSpec pre post invariants variants) quotedHelper 128))
    (s : Store H) (caller : Frame) (callee : ModuleInst) (ptr sp : BitVec 32) (value : UInt64)
    (address globalAddress : Nat) (mem : MemInst) (globalType : CGlobalType)
    (mapped : s.mem? (callFrame callee quotedHelper ptr value) ⟨0⟩ = some (address, mem))
    (global : s.global? (callFrame callee quotedHelper ptr value) ⟨0⟩ =
      some (globalAddress, ⟨globalType, .i32 sp⟩))
    (preH : let ρ := helperEnv ptr sp value mem.bytes
      (helperSpec pre post invariants variants).preF.den F ρ ρ)
    (result : BitVec 32) (bytes : ByteArray)
    (postH : ∀ final word stackWord,
      post.den F (helperEnv ptr sp value mem.bytes) (valEnv [.i32 word, .i32 stackWord] final) →
      word = result ∧ stackWord = sp ∧ final = bytes) :
    Steps P host ⟨s, caller, [activation callee quotedHelper ptr value]⟩
      ⟨s.setMem address { mem with bytes := bytes }, caller, [constI32 result]⟩ := by
  unfold Store.mem? at mapped
  obtain ⟨a, memLink, rest⟩ := Option.bind_eq_some_iff.mp mapped
  obtain ⟨m, memEntry, pair⟩ := Option.bind_eq_some_iff.mp rest
  rcases Prod.mk.inj (Option.some.inj pair) with ⟨rfl, rfl⟩
  unfold Store.global? at global
  obtain ⟨g, globLink, rest⟩ := Option.bind_eq_some_iff.mp global
  obtain ⟨gi, globEntry, pair⟩ := Option.bind_eq_some_iff.mp rest
  rcases Prod.mk.inj (Option.some.inj pair) with ⟨rfl, rfl⟩
  change callee.mems[0]? = some a at memLink
  change callee.globals[0]? = some g at globLink
  let S := helperSpec pre post invariants variants
  let ρ := helperEnv ptr sp value m.bytes
  let fi : FuncInst H := ⟨default, callee, .wasm quotedHelper⟩
  have hm : MemOk S s callee (ρ.mem 0) := ⟨a, m, memLink, memEntry, rfl⟩
  have hg : GlobOk S s callee ρ := by
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
        exact ⟨g, _, globLink, globEntry, rfl⟩
      | succ g => simp at lookup
  have locals : Silmaril.Wasm.Auto.VCGen.intTys? quotedHelper.locals = some [.i32, .i32, .i32] := by kernel_rfl
  have vc : AllValid F
      (gen S (S.params ++ [.i32, .i32, .i32] ++ S.globals) 128 []
        (endVC S (S.params ++ [.i32, .i32, .i32] ++ S.globals)) 0
        quotedHelper.body (initSt S [.i32, .i32, .i32])) := by
    unfold genFunc at validConditions
    rw [locals, wellScoped] at validConditions
    exact validConditions
  have body := body_wp (c := .total) (fi := fi) (P := P) (host := host) locals wellScoped
    (fun _ => rfl) vc (s := s) (ρ₀ := ρ) (by simp [CallsOK, helperSpec]) hm hg preH
  let outcomePost := callPost caller [] ((fspec F S 0 fi).post s (argsOf S ρ))
  have bodySafe : TSafe P host (bodyPostT P host 1 caller [] outcomePost)
      ⟨s, callFrame callee quotedHelper ptr value,
        expression quotedHelper.body⟩ := by
    refine TSafe.post_mono body ?_
    intro s' f' o ho
    exact bodyPostT_of_postOf (fi := fi) (a := 0) wellScoped rfl rfl hm hg
      (drop_lt_init [.i32, .i32, .i32]) ho
  have packed : TSafe P host outcomePost
      ⟨s, caller, [activation callee quotedHelper ptr value]⟩ :=
    TSafe.frame (TSafe.label bodySafe)
  obtain ⟨⟨s', f', code⟩, outcome, steps, exits, outcomePostH⟩ := reachExit packed
  obtain ⟨rfl, normal | trapped | thrown⟩ := outcomePostH
  · obtain ⟨values, rfl, returned⟩ := normal
    obtain ⟨B, G, store, globalTypes, res, same, _, resultTypes, facts⟩ := returned
    cases same
    obtain ⟨word, rfl⟩ := singleI32 values resultTypes
    obtain ⟨sp', rfl⟩ := singleI32 G globalTypes
    obtain ⟨resultWord, stackWord, finalBytes⟩ := postH B word sp' (facts ρ rfl hm hg)
    subst word sp' B
    have unchanged : setGs (upd S s callee bytes) callee
        [.i32 sp] = upd S s callee bytes := by
      apply setGs_self
      intro i bound
      have eq : i = 0 := by change i < 1 at bound; omega
      subst i
      refine ⟨g, ⟨globalType, .i32 sp⟩, globLink, ?_, rfl⟩
      change (setM s callee _).globals[g]? = _
      rw [setM_some memLink memEntry]
      exact globEntry
    rw [unchanged] at store
    change s' = setM s callee bytes at store
    rw [setM_some memLink memEntry] at store
    change code = [constI32 result] at exits
    subst s' code
    exact steps
  · obtain ⟨_, _, _, _, _, _, impossible, _⟩ := trapped
    cases impossible
  · obtain ⟨_, _, _, _, _, _, _, impossible, _⟩ := thrown
    cases impossible

/-- The original reactor Code record at 547 selects the helper verified here. -/
theorem originalHelper : sourceFunction? original 547 = some quotedHelper :=
  originalPutVarintLongFunction.trans (by kernel_rfl)

/-- The entered quoted helper executes both ordinary loops for the stated width,
preserving all state outside the two specified byte writes. -/
theorem helper_ordinary {H : Type} {P : Numerics.Profile} {host : HostSemantics H}
    (s : Store H) (caller : Frame) (callee : ModuleInst) (ptr sp : BitVec 32)
    (value : UInt64) (width address globalAddress : Nat) (mem : MemInst) (globalType : CGlobalType)
    (fits : Width value.toNat width)
    (mapped : s.mem? (callFrame callee quotedHelper ptr value) ⟨0⟩ = some (address, mem))
    (global : s.global? (callFrame callee quotedHelper ptr value) ⟨0⟩ =
      some (globalAddress, ⟨globalType, .i32 sp⟩))
    (buffers : Buffers mem.bytes ptr sp width) :
    Steps P host ⟨s, caller, [activation callee quotedHelper ptr value]⟩
      ⟨postStore s address mem ptr sp value, caller, [constI32 (BitVec.ofNat 32 width)]⟩ := by
  refine helperSteps_of_vcs (F := model width) symPre symPost _ _
    (show spec.wellScoped = true by kernel_rfl) (valid width)
    s caller callee ptr sp value address globalAddress mem globalType mapped global
    ?_ (BitVec.ofNat 32 width) (outputBytes mem.bytes ptr sp value) ?_
  · change Width (joinHalves (value.toBitVec.setWidth 32) ((value.toBitVec >>> 32).setWidth 32))
      width ∧ Buffers mem.bytes ptr sp width
    rw [joinSplit, UInt64.toNat_toBitVec]
    exact ⟨fits, buffers⟩
  · intro final word stackWord observed
    change word = BitVec.ofNat 32 width ∧ stackWord = sp ∧
      final = outputBytes mem.bytes ptr sp
        (UInt64.ofNat (joinHalves (value.toBitVec.setWidth 32) ((value.toBitVec >>> 32).setWidth 32)))
      at observed
    rwa [joinSplit, UInt64.toNat_toBitVec, UInt64.ofNat_toNat] at observed

/-- The quoted reactor wrapper writes the ordinary encoding for widths three through
eight, with exact scratch and caller-frame effects. -/
theorem putVarint_ordinary {H : Type} {P : Numerics.Profile} {host : HostSemantics H}
    {s : Store H} {caller : Frame} {putFn : Func} {putAddress helperAddress : Nat}
    {putInstance helperInstance : FuncInst H} {ptr sp : BitVec 32} {value : UInt64}
    {width address globalAddress : Nat} {mem : MemInst} {globalType : CGlobalType}
    (selected : definedFunction? sqlite 530 = some putFn)
    (putBinding : s.func? caller ⟨530⟩ = some (putAddress, putInstance))
    (helperBinding : s.func? (callFrame putInstance.module putFn ptr value) ⟨547⟩ =
      some (helperAddress, helperInstance))
    (putCode : putInstance.code = .wasm putFn)
    (helperCode : helperInstance.code = .wasm quotedHelper)
    (putType : Expand putInstance.type (.func (.cons Ty.i32 (.cons Ty.i64 .nil)) (.cons Ty.i32 .nil)))
    (helperType : Expand helperInstance.type (.func (.cons Ty.i32 (.cons Ty.i64 .nil)) (.cons Ty.i32 .nil)))
    (entered : 3 ≤ width) (fits : Width value.toNat width)
    (mapped : s.mem? (callFrame helperInstance.module quotedHelper ptr value) ⟨0⟩ =
      some (address, mem))
    (global : s.global? (callFrame helperInstance.module quotedHelper ptr value) ⟨0⟩ =
      some (globalAddress, ⟨globalType, .i32 sp⟩))
    (buffers : Buffers mem.bytes ptr sp width) :
    Steps P host ⟨s, caller, vals (args ptr value) ++ [.plain (.call ⟨530⟩)]⟩
      ⟨postStore s address mem ptr sp value, caller, [constI32 (BitVec.ofNat 32 width)]⟩ := by
  have low : 16384 ≤ value.toNat := (show 128 ^ 2 ≤ 128 ^ (width - 1) from
    Nat.pow_le_pow_right (by decide) (by omega)).trans fits.lower
  exact putVarint_forward selected putBinding helperBinding putCode helperCode putType helperType low
    (helper_ordinary s (callFrame putInstance.module putFn ptr value) helperInstance.module ptr sp value
      width address globalAddress mem globalType fits mapped global buffers)

#print axioms helperSteps_of_vcs
#print axioms originalHelper
#print axioms helper_ordinary
#print axioms putVarint_ordinary

end SqliteWasm.OrdinaryVarint
