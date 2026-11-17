module

public import Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Ring.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.Take
public import Silmaril.Wasm.Logic.Instr.Thms
public import Silmaril.Wasm.Logic.Memory.Thms

/-!
# `chunkRing` meets its chunk specification

* `ring_shape`: the instance has shape `MShape` (kernel evaluation); `ring_mems`: both exported
  functions see memory `0`; `ringInv_init`: the instantiated store represents the empty buffer;
  `ringInv_uniq`: a store represents at most one buffer (the count and the loads determine it);
* rules for the memory instructions of the example (`X.load64`, `X.store64R`) and for `rem_u`,
  `mul`, `sub`; slot arithmetic (`slot_addr`, `slot_ne`, `slot_shift`);
* `chunkRing_sat`: in every environment `ρ` and every profile, assuming the writer answers agree
  with `ρ` (no writer sentinel), the instance meets `chunkSSpec ringPix ppol ρ takeR ringInv`:
  `feed(x)` stores `x` in the slot after the buffered values and moves the represented buffer
  from `g` to `g ++ [x]` (or diverges with eight values buffered); `finish(n)` with `n = 0` or
  `n` above the count returns `(0, h)`, `h` denoting `()`, keeping the buffer; otherwise its loop
  (invariant `RingLoop`: the accumulated handle denotes the list of the buffered values
  `i … n - 1`) builds the list of the first `n` buffered values, and the call returns `(n, h)`
  and drops them from the buffer by advancing the start slot. Traps keep the buffer.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.Ring

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics
  Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.GameLink
  Silmaril.Formats Silmaril.Formats.Api Silmaril.Accept.Handle Silmaril.Accept.Parse
  Silmaril.Accept.Mixed Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Writers Silmaril.Wasm.Game.HandleAccept.Writers.Builders
  Silmaril.Wasm.Game.HandleAccept.Parsing Silmaril.Wasm.Game.HandleAccept.Mixed.Stream
  Silmaril.Wasm.Game.HandleAccept.Mixed.Stream.Stack Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk
  Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Take
  Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Ring
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers
  Silmaril.Proofs.Wasm.Game.HandleAccept.Parsing.Checkers
  Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.TwoWords
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream.Stack
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.Take
open Silmaril.Wasm.Logic.Strategy (ISpec)
open Silmaril.Wasm.Logic.Core (Outcome Post Region)

/-! ## The instance -/

/-- The exported functions. -/
abbrev ringFns : List (List ValType × List Instr × List (Option Val)) :=
  [([], ringFeedBody, []), ([.i32, .i32], ringFinBody, [some (.i32 0), some (.i32 0)])]

theorem ring_shape : MShape (Verify.instOf chunkRing) twoFTs chunkFTs ringFns [0, 1] :=
  MShape.of_ok (by decide +kernel)

theorem ring_mems4 :
    ((Verify.instOf chunkRing).store.funcs[4]?).map (·.module.mems) = some [0] := by
  decide +kernel

theorem ring_mems5 :
    ((Verify.instOf chunkRing).store.funcs[5]?).map (·.module.mems) = some [0] := by
  decide +kernel

theorem ring_gval0 : gval (Verify.instOf chunkRing).store 0 = some (.i32 0) := by
  decide +kernel

theorem ring_gval1 : gval (Verify.instOf chunkRing).store 1 = some (.i32 0) := by
  decide +kernel

theorem ring_memlen : (Verify.instOf chunkRing).store.mems.length = 1 := by
  decide +kernel

theorem ringInv_init : ringInv [] (Verify.instOf chunkRing).store :=
  ⟨rfl, 0, 0, ring_gval0, ring_gval1, by decide, rfl, by decide, ring_memlen,
    fun _ hi => absurd hi (Nat.not_lt_zero _)⟩

theorem ringInv_uniq {g g' : List (BitVec 64)} {s : Store Nat} (h : ringInv g s)
    (h' : ringInv g' s) : g = g' := by
  obtain ⟨-, st, cnt, h0, h1, -, hc, -, -, hl⟩ := h
  obtain ⟨-, st', cnt', h0', h1', -, hc', -, -, hl'⟩ := h'
  rw [h0] at h0'
  rw [h1] at h1'
  cases h0'
  cases h1'
  have hlen : g.length = g'.length := hc.symm.trans hc'
  refine List.ext_getElem hlen fun i hi hi' => ?_
  obtain ⟨mi, hmi, hld⟩ := hl i hi
  obtain ⟨mi', hmi', hld'⟩ := hl' i hi'
  rw [hmi] at hmi'
  cases hmi'
  rw [hld] at hld'
  exact Option.some.inj hld'

/-! ## Slots -/

theorem slot_addr {st k : BitVec 32} (hs : st.toNat < cap) (hk : k.toNat < cap) :
    ((st + k) % 8 * 8).toNat = slot st.toNat k.toNat := by
  have h8 : (8 : BitVec 32).toNat = 8 := rfl
  have hs' : st.toNat < 8 := hs
  have hk' : k.toNat < 8 := hk
  simp only [slot, cap]
  simp only [BitVec.toNat_mul, BitVec.toNat_umod, BitVec.toNat_add, h8]
  omega

theorem slot_ne {st i j : Nat} (hi : i < cap) (hj : j < cap) (hij : i ≠ j) :
    Region.Disjoint ⟨slot st i, 8⟩ ⟨slot st j, 8⟩ := by
  simp only [Region.Disjoint, Region.stop, slot, cap] at *
  omega

theorem slot_shift (st n j : Nat) : slot ((st + n) % cap) j = slot st (n + j) := by
  simp only [slot, cap]
  omega

theorem st_next {st n : BitVec 32} (hs : st.toNat < cap) (hn : n.toNat ≤ cap) :
    ((st + n) % 8).toNat = (st.toNat + n.toNat) % cap ∧ (st.toNat + n.toNat) % cap < cap := by
  have h8 : (8 : BitVec 32).toNat = 8 := rfl
  have hs' : st.toNat < 8 := hs
  have hn' : n.toNat ≤ 8 := hn
  simp only [cap]
  constructor
  · simp only [BitVec.toNat_umod, BitVec.toNat_add, h8]
    omega
  · omega

theorem cnt_sub {c n : BitVec 32} (h : n.toNat ≤ c.toNat) : (c - n).toNat = c.toNat - n.toNat := by
  rw [BitVec.toNat_sub]
  omega

theorem cnt_succ {c : BitVec 32} (h : c.toNat < cap) : (c + 1).toNat = c.toNat + 1 := by
  have h1 : (1 : BitVec 32).toNat = 1 := rfl
  simp only [cap] at h
  rw [BitVec.toNat_add, h1]
  omega

theorem i_pred {i : BitVec 32} (h : i ≠ 0) : (i + BitVec.allOnes 32).toNat = i.toNat - 1 ∧
    i.toNat - 1 < i.toNat := by
  have hz : i.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq (by rw [h']; rfl))
  have ha : (BitVec.allOnes 32).toNat = 4294967295 := rfl
  have hl : i.toNat < 4294967296 := i.isLt
  rw [BitVec.toNat_add, ha]
  constructor <;> omega

/-! ## Rules -/

section Rules

variable {P : Profile} {host : HostSemantics Nat} {s : Store Nat} {F : Frame} {us : List Val}
  {is : List Instr} {Q : Post Nat}

theorem X.remu8 {x : BitVec 32}
    (h : HWP P host s F (vals (us ++ [.i32 (x % 8)]) ++ expression is) Q) :
    HWP P host s F (vals (us ++ [.i32 x]) ++
      expression (.intConst .i32 8 :: .intBinOp .i32 (.rem .unsigned) :: is)) Q := by
  refine X.i32Const ?_
  rw [List.append_assoc]
  exact Wp.intBinOp (m := .part) (t := .i32) (x := x) (y := 8) (z := (x % 8 : BitVec 32))
    rfl h

theorem X.mul8 {x : BitVec 32}
    (h : HWP P host s F (vals (us ++ [.i32 (x * 8)]) ++ expression is) Q) :
    HWP P host s F (vals (us ++ [.i32 x]) ++
      expression (.intConst .i32 8 :: .intBinOp .i32 .mul :: is)) Q := by
  refine X.i32Const ?_
  rw [List.append_assoc]
  exact Wp.intBinOp (m := .part) (t := .i32) (x := x) (y := 8) (z := (x * 8 : BitVec 32)) rfl h

theorem X.sub32 {x y : BitVec 32}
    (h : HWP P host s F (vals (us ++ [.i32 (x - y)]) ++ expression is) Q) :
    HWP P host s F (vals (us ++ [.i32 x] ++ [.i32 y]) ++ expression (.intBinOp .i32 .sub :: is))
      Q := by
  rw [List.append_assoc]
  exact Wp.intBinOp (m := .part) (t := .i32) (x := x) (y := y) (z := x - y) rfl h

theorem mem?_of {F : Frame} (hF : F.module.mems = [0]) {mi : MemInst}
    (hmi : s.mems[0]? = some mi) : s.mem? F ⟨0⟩ = some (0, mi) := by
  simp only [Store.mem?, hF]
  rw [show ([0] : List Nat)[(⟨0⟩ : MemIdx).toNat]? = some 0 from rfl]
  simp [hmi]

theorem store_none_lt {B : ByteArray} {a n : Nat} {w : BitVec (8 * n)}
    (h : Memory.store B a w = none) : B.size < a + n := by
  unfold Memory.store Memory.writeBytes at h
  split at h
  · cases h
  · rename_i hb
    rw [Memory.encodeLE_size] at hb
    omega

/-- A full-width `i64` load from memory `0` of a store with one memory. -/
theorem X.load64 {addr : BitVec 32} (hF : F.module.mems = [0]) (hl : s.mems.length = 1)
    (htrap : Q s F .trap)
    (h : ∀ mi c, s.mems[0]? = some mi →
      Memory.load mi.bytes addr.toNat 8 = some c →
      HWP P host s F (vals (us ++ [.i64 c]) ++ expression is) Q) :
    HWP P host s F (vals (us ++ [.i32 addr]) ++ expression (.intLoad .i64 none ⟨0⟩ ⟨0, 0⟩ :: is))
      Q := by
  obtain ⟨mi, hmi⟩ : ∃ mi, s.mems[0]? = some mi :=
    ⟨s.mems[0]'(by omega), List.getElem?_eq_getElem _⟩
  have hm := mem?_of hF hmi
  rcases hld : Memory.load mi.bytes (effAddr addr.toNat ⟨0, 0⟩) (IntType.i64.width / 8) with
    _ | c
  · refine Wp.intLoad_oob (m := .part) (a := .i32) (i := addr) (t := .i64) hm ?_ htrap
    unfold Memory.load Memory.readBytes at hld
    split at hld
    · cases hld
    · rename_i hb
      exact Nat.lt_of_not_le hb
  · refine Wp.intLoad (m := .part) (a := .i32) (i := addr) (t := .i64) hm hld ?_
    exact h mi c hmi hld

/-- A full-width `i64` store to memory `0` of a store with one memory. -/
theorem X.store64R {addr : BitVec 32} {v : BitVec 64} (hF : F.module.mems = [0])
    (hl : s.mems.length = 1) (htrap : Q s F .trap)
    (h : ∀ mi b, s.mems[0]? = some mi →
      Memory.store mi.bytes addr.toNat (count := 8) v = some b →
      HWP P host (s.setMem 0 { mi with bytes := b }) F (vals us ++ expression is) Q) :
    HWP P host s F (vals (us ++ [.i32 addr, .i64 v]) ++
      expression (.intStore .i64 none ⟨0⟩ ⟨0, 0⟩ :: is)) Q := by
  obtain ⟨mi, hmi⟩ : ∃ mi, s.mems[0]? = some mi :=
    ⟨s.mems[0]'(by omega), List.getElem?_eq_getElem _⟩
  have hm := mem?_of hF hmi
  rcases hst : Memory.store mi.bytes (effAddr addr.toNat ⟨0, 0⟩)
    (count := IntType.i64.width / 8) (v.setWidth _) with _ | b
  · exact Wp.intStore_oob (m := .part) (a := .i32) (i := addr) (t := .i64) (c := v)
      hm (store_none_lt hst) htrap
  · exact Wp.intStore (m := .part) (a := .i32) (i := addr) (t := .i64) (c := v) hm hst
      (h mi b hmi hst)

end Rules

theorem setMem_mems {s : Store Nat} {mi : MemInst} (hl : s.mems.length = 1) :
    (s.setMem 0 mi).mems[0]? = some mi ∧ (s.setMem 0 mi).mems.length = 1 ∧
      (s.setMem 0 mi).funcs = s.funcs ∧ (s.setMem 0 mi).globals = s.globals := by
  simp [Store.setMem, hl]

@[simp] theorem setGlobal_mems (s : Store Nat) (a : Nat) (v : Val) :
    (s.setGlobal a v).mems = s.mems := rfl

theorem gval_setMem {s : Store Nat} {mi : MemInst} (a : Nat) :
    gval (s.setMem 0 mi) a = gval s a := rfl

theorem Traps.loop {Q : Post Nat} {s : Store Nat} {Inv : Store Nat → Frame → List Val → Prop}
    (h : Traps Q s) : Traps (loopPost 0 [] Inv Q) s := fun f => ⟨(h f).1, (h f).2⟩

/-! ## Decoding -/

theorem rdec_feed {ts : List FnType} {e : (ifaceSig ts).Op} {v : (ifaceSig ts).Ar e}
    {x : BitVec 64} (he : e.1.val = 0) (hx : e.2.1 = [.i64 x]) (hv : ansVals v = some []) :
    parseDec ringPix e v = some (.feed [x]) := by
  simp [parseDec, ringPix, hv, he, hx, i64Val, Writers.i64Arg, Val.i64]

theorem rdec_finish {ts : List FnType} {e : (ifaceSig ts).Op} {v : (ifaceSig ts).Ar e}
    {u h : BitVec 32} (he : e.1.val = 1) (hv : ansVals v = some [.i32 u, .i32 h]) :
    parseDec ringPix e v = some (.finish u.toNat h) := by
  simp [parseDec, ringPix, hv, he, i32Two, Val.i32]

/-! ## Lists -/

theorem ofAtoms_drop_pred {g : List (BitVec 64)} {i : Nat} (hi : 0 < i) (hlen : i ≤ g.length) :
    SExp2.ofAtoms (g.drop (i - 1)) =
      .cons (.atom (g[i - 1]'(by omega))) (SExp2.ofAtoms (g.drop i)) := by
  rw [List.drop_eq_getElem_cons (by omega)]
  have : i - 1 + 1 = i := by omega
  rw [this]
  rfl

/-! ## The module -/

abbrev RI : ScalarInstance := Verify.instOf chunkRing

/-- The invariant of `finish`'s loop, from the store `s` and the frame's module `mi`: the store
is unchanged, `i ≤ n`, and `acc` denotes the list of the buffered values `i … n - 1`. -/
def RingLoop (ρ : Env (BitVec 32) (SExp2 (BitVec 64))) (g : List (BitVec 64)) (n : BitVec 32)
    (s₀ : Store Nat) (mi : ModuleInst) (s : Store Nat) (f : Frame) : Prop :=
  s = s₀ ∧ ∃ i acc : BitVec 32, f = ⟨[some (.i32 n), some (.i32 i), some (.i32 acc)], mi⟩ ∧
    i.toNat ≤ n.toNat ∧ ρ acc = some (SExp2.ofAtoms ((g.take n.toNat).drop i.toNat))

/-- **`chunkRing` meets its chunk specification** in every environment and every profile. -/
theorem chunkRing_sat (P : Profile) (ρ : Env (BitVec 32) (SExp2 (BitVec 64)))
    (ppol : PPolicy (BitVec 32)) :
    SGameSat P RI (WSpec RI ρ Set.univ) (chunkSSpec ringPix ppol ρ takeR ringInv) := by
  have hS := ring_shape
  refine sgameSat_ofM hS (fun g s h => h.1) (fun g g' s h h' => ringInv_uniq h h')
    (fun g e v hv => ⟨fun e' hd => by simp [parseDec, hv] at hd, by
      simp [chunkSSpec, chunkNext, parseDec, hv]⟩)
    fun j fi s args ht g Q hfi hm hmg hinv hT hret => ?_
  obtain ⟨hfs, st, cnt, hrep⟩ := hinv
  have hlen : RI.exports.length = 2 := by rw [hS.exports]; rfl
  have hgj := hS.get j
  obtain ⟨j, hj⟩ := j
  have hj2 : j < 2 := hlen ▸ hj
  match j, hj2 with
  | 0, _ =>
    -- `feed(x)`
    have hFm : fi.module.mems = [0] := by
      have h4 := ring_mems4
      rw [show (twoFTs.length + 0) = 4 from rfl] at hfi
      rw [hfi] at h4
      exact Option.some.inj h4
    have ht' := ht
    rw [hgj] at ht'
    obtain ⟨x, rfl⟩ : ∃ x, args = [.i64 x] := by
      rcases ht' with _ | ⟨⟨x, rfl⟩, hnil⟩
      cases hnil
      exact ⟨x, rfl⟩
    have hinv : ringInv g s := ⟨hfs, st, cnt, hrep⟩
    obtain ⟨h0, h1, hst, hcg, hgc, hml, hld⟩ := hrep
    show HWP P _ s ⟨[some (.i64 x)], fi.module⟩ (vals [] ++ expression ringFeedBody) Q
    simp only [ringFeedBody, ringGuard, slotAddr, List.cons_append, List.nil_append]
    refine X.globalGet (us := []) (x := ⟨1⟩) (a := 1) (by rw [hmg]; rfl) h1 ?_
    refine X.i32Const (us := [] ++ [.i32 cnt]) ?_
    refine X.rel32 (us := []) ?_
    refine X.if_ (us := []) (fun _ => ?_) (fun hc => ?_)
    · refine X.loop (Inv := fun _ _ => True) (fun _ _ _ => ?_) trivial
      exact HWP.of_exits (o := .br 0 []) ⟨⟨0⟩, [], rfl, rfl⟩ ⟨[], [], rfl, rfl, rfl, trivial⟩
    · have hc8 := rel_eq_z hc
      have hlt : cnt.toNat < cap := by
        simp only [cap] at hgc ⊢
        have : cnt.toNat ≠ 8 := fun h => hc8 (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
        omega
      have hn : ∀ v : Answer (RI.exports.get ⟨0, hj⟩), v.toResult = .values [] →
          chunkNext (I := RI) ringPix g ⟨⟨0, hj⟩, ⟨[.i64 x], ht⟩⟩ v = g ++ [x] := fun v hv => by
        simp [chunkNext, rdec_feed (ts := RI.exports) (e := ⟨⟨0, hj⟩, ⟨[.i64 x], ht⟩⟩) rfl rfl
          (ansVals_of hv), chunkStep]
      have hpost : ∀ v : Answer (RI.exports.get ⟨0, hj⟩), v.toResult = .values [] →
          (chunkSSpec (I := RI) ringPix ppol ρ takeR ringInv).post g
            ⟨⟨0, hj⟩, ⟨[.i64 x], ht⟩⟩ v := fun v hv e hd => by
        rw [rdec_feed rfl rfl (ansVals_of hv)] at hd
        cases hd
        intro ps w h ps' _ hR
        exact hR.elim
      refine X.globalGet (us := []) (x := ⟨0⟩) (a := 0) (by rw [hmg]; rfl) h0 ?_
      refine X.globalGet (us := [] ++ [.i32 st]) (f := ⟨[some (.i64 x)], fi.module⟩) (x := ⟨1⟩)
        (a := 1) (by rw [hmg]; rfl) h1 ?_
      refine X.add32 (us := []) ?_
      refine X.remu8 (us := []) ?_
      refine X.mul8 (us := []) ?_
      refine X.localGet (x := ⟨0⟩) (v := .i64 x) rfl ?_
      refine X.store64R (us := []) hFm hml ((hT s hinv _).1) fun mi b hmi hstb => ?_
      obtain ⟨hmi', hml', hfs', hgl'⟩ := setMem_mems (mi := { mi with bytes := b }) hml
      let s₁ := s.setMem 0 { mi with bytes := b }
      refine X.globalGet (s := s₁) (f := ⟨[some (.i64 x)], fi.module⟩) (us := []) (x := ⟨1⟩)
        (a := 1) (v := .i32 cnt)
        (by rw [hmg]; rfl) (by rw [gval_setMem]; exact h1) ?_
      refine X.i32Const (us := [] ++ [.i32 cnt]) ?_
      refine X.add32 (us := []) ?_
      refine X.globalSet (s := s₁) (f := ⟨[some (.i64 x)], fi.module⟩) (us := []) (x := ⟨1⟩)
        (a := 1) (by rw [hmg]; rfl)
        (by rw [gval_setMem, h1]; rfl) ?_
      refine X.return_ (hret _ _ [] (by rw [hgj]; rfl) fun v hv => ⟨hpost v hv, ?_⟩)
      show ringInv (chunkNext (I := RI) ringPix g ⟨⟨0, hj⟩, ⟨[.i64 x], ht⟩⟩ v) _
      rw [hn v hv]
      have haddr := slot_addr hst hlt
      rw [haddr] at hstb
      refine ⟨by rw [setGlobal_funcs, hfs', hfs], st, cnt + 1, ?_, ?_, hst, ?_, ?_, ?_, ?_⟩
      · rw [gval_setGlobal, gval_setMem]; simpa using h0
      · rw [gval_setGlobal, gval_setMem, h1]; rfl
      · rw [cnt_succ hlt, hcg]; simp
      · simp only [List.length_append, List.length_singleton]
        omega
      · rw [setGlobal_mems]; exact hml'
      · intro i hi
        refine ⟨{ mi with bytes := b }, by rw [setGlobal_mems]; exact hmi', ?_⟩
        simp only [List.length_append, List.length_singleton] at hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · obtain ⟨mi₀, hmi₀, hl₀⟩ := hld i hi
          rw [hmi] at hmi₀
          cases hmi₀
          rw [List.getElem_append_left hi]
          show Memory.load b _ 8 = _
          rw [Silmaril.Wasm.Logic.Core.load_store_disjoint hstb
            (slot_ne hlt (by omega) (by omega))]
          exact hl₀
        · rw [List.getElem_append_right (Nat.le_refl _)]
          simp only [Nat.sub_self, List.getElem_singleton]
          rw [← hcg]
          exact Silmaril.Wasm.Logic.Core.load_store_same hstb
  | 1, _ =>
    -- `finish(n)`
    have hFm : fi.module.mems = [0] := by
      have h5 := ring_mems5
      rw [show (twoFTs.length + 1) = 5 from rfl] at hfi
      rw [hfi] at h5
      exact Option.some.inj h5
    have ht' := ht
    rw [hgj] at ht'
    obtain ⟨n, rfl⟩ : ∃ n, args = [.i32 n] := by
      rcases ht' with _ | ⟨⟨n, rfl⟩, hnil⟩
      cases hnil
      exact ⟨n, rfl⟩
    have hinv : ringInv g s := ⟨hfs, st, cnt, hrep⟩
    have hT₀ := hT s hinv
    obtain ⟨h0, h1, hst, hcg, hgc, hml, hld⟩ := hrep
    -- the returns of `finish(n)`, by their answer
    have hpost : ∀ (u r : BitVec 32) (y : SExp2 (BitVec 64)), ρ r = some y →
        (u.toNat ≤ g.length → y = SExp2.ofAtoms (g.take u.toNat)) →
        ∀ v : Answer (RI.exports.get ⟨1, hj⟩), v.toResult = .values [.i32 u, .i32 r] →
        (chunkSSpec (I := RI) ringPix ppol ρ takeR ringInv).post g
          ⟨⟨1, hj⟩, ⟨[.i32 n], ht⟩⟩ v := fun u r y hy hu v hv e hd => by
      rw [rdec_finish rfl (ansVals_of hv)] at hd
      cases hd
      intro ps w h ps' hps hR _ y' hy'
      obtain ⟨hl, rfl, rfl, -⟩ := hR
      rw [hy] at hy'
      cases hy'
      rw [hps] at hl ⊢
      exact hu hl
    have hnext : ∀ (u r : BitVec 32) (v : Answer (RI.exports.get ⟨1, hj⟩)),
        v.toResult = .values [.i32 u, .i32 r] →
        chunkNext (I := RI) ringPix g ⟨⟨1, hj⟩, ⟨[.i32 n], ht⟩⟩ v =
          chunkStep g (.finish u.toNat r) := fun u r v hv => by
      simp [chunkNext, rdec_finish (ts := RI.exports) (e := ⟨⟨1, hj⟩, ⟨[.i32 n], ht⟩⟩) rfl
        (ansVals_of hv)]
    show HWP P _ s ⟨[some (.i32 n), some (.i32 0), some (.i32 0)], fi.module⟩
      (vals [] ++ expression ringFinBody) Q
    simp only [ringFinBody]
    refine X.localGet (x := ⟨0⟩) (v := .i32 n) rfl ?_
    refine X.globalGet (us := [] ++ [.i32 n])
      (f := ⟨[some (.i32 n), some (.i32 0), some (.i32 0)], fi.module⟩) (x := ⟨1⟩) (a := 1)
      (by rw [hmg]; rfl) h1 ?_
    refine X.rel32 (us := []) ?_
    refine X.if_ (us := []) (fun _ => ?_) (fun hc => ?_)
    · -- `n > count`: nothing is consumed
      refine X.i32Const (us := []) ?_
      refine X.wNilM (us := [.i32 0]) hS hfs hm (Traps.label hT₀) fun r hr => ?_
      refine X.return_ (hret _ _ [.i32 0, .i32 r] (by rw [hgj]; rfl) fun v hv =>
        ⟨hpost 0 r _ hr (fun _ => by simp [SExp2.ofAtoms, SExp2.ofList]) v hv, ?_⟩)
      show ringInv (chunkNext (I := RI) ringPix g ⟨⟨1, hj⟩, ⟨[.i32 n], ht⟩⟩ v) _
      rw [hnext 0 r v hv]
      simpa [chunkStep] using hinv
    · have hnc := rel_gtu_z hc
      refine X.localGet (x := ⟨0⟩) (v := .i32 n) rfl ?_
      refine X.eqz (us := []) ?_
      refine X.if_ (us := []) (fun _ => ?_) (fun hc₀ => ?_)
      · -- `n = 0`: nothing is consumed
        refine X.i32Const (us := []) ?_
        refine X.wNilM (us := [.i32 0]) hS hfs hm (Traps.label hT₀) fun r hr => ?_
        refine X.return_ (hret _ _ [.i32 0, .i32 r] (by rw [hgj]; rfl) fun v hv =>
          ⟨hpost 0 r _ hr (fun _ => by simp [SExp2.ofAtoms, SExp2.ofList]) v hv, ?_⟩)
        show ringInv (chunkNext (I := RI) ringPix g ⟨⟨1, hj⟩, ⟨[.i32 n], ht⟩⟩ v) _
        rw [hnext 0 r v hv]
        simpa [chunkStep] using hinv
      · -- `0 < n ≤ count`: the loop
        have hn0 := eqz_z hc₀
        have hng : n.toNat ≤ g.length := hcg ▸ hnc
        refine X.wNilM (us := []) hS hfs hm hT₀ fun r₀ hr₀ => ?_
        refine X.localSet (x := ⟨2⟩) (by exact (by decide : (2 : Nat) < 3)) ?_
        refine X.localGet (x := ⟨0⟩) (v := .i32 n) rfl ?_
        refine X.localSet (x := ⟨1⟩) (by exact (by decide : (1 : Nat) < 3)) ?_
        refine HWP.block (us := []) (vs := []) (bt := .empty) (t₁ := []) (t₂ := [])
          (rest := expression [.unreachable]) rfl rfl ?_
        have hTL : Traps (labelPost P (gameHost RI (WSpec RI ρ Set.univ)) 0 [] []
            (seqPost P (gameHost RI (WSpec RI ρ Set.univ)) (expression [.unreachable]) Q)) s :=
          Traps.label hT₀
        refine X.loop (Inv := RingLoop ρ g n s fi.module)
          (fun s' f hI => ?_) ⟨rfl, n, r₀, rfl, le_rfl, by
            rw [List.drop_of_length_le (by simp)]; simpa [SExp2.ofAtoms, SExp2.ofList] using hr₀⟩
        obtain ⟨rfl, i, acc, rfl, hin, hacc⟩ := hI
        have hTo := Traps.loop (Inv := fun s'' f vs => vs = [] ∧ RingLoop ρ g n s' fi.module s'' f)
          hTL
        simp only [ringLoopBody, slotAddr, List.cons_append, List.nil_append]
        refine X.localGet (x := ⟨1⟩) (v := .i32 i) rfl ?_
        refine X.eqz (us := []) ?_
        refine X.if_ (us := []) (fun hi0 => ?_) (fun hi0 => ?_)
        · -- `i = 0`: advance the start slot, drop `n` values, return
          have hi : i = 0 := by simpa using bool32_ne_zero hi0
          subst hi
          let F : Frame := ⟨[some (.i32 n), some (.i32 0), some (.i32 acc)], fi.module⟩
          obtain ⟨hst', hstl⟩ := st_next hst (by omega : n.toNat ≤ cap)
          refine X.globalGet (f := F) (us := []) (x := ⟨0⟩) (a := 0) (by rw [hmg]; rfl) h0 ?_
          refine X.localGet (x := ⟨0⟩) (v := .i32 n) rfl ?_
          refine X.add32 (us := []) ?_
          refine X.remu8 (us := []) ?_
          refine X.globalSet (s := s') (f := F) (us := []) (x := ⟨0⟩) (a := 0)
            (by rw [hmg]; rfl) (by simp [h0]) ?_
          let s₁ := s'.setGlobal 0 (.i32 ((st + n) % 8))
          refine X.globalGet (s := s₁) (f := F) (us := []) (x := ⟨1⟩) (a := 1) (v := .i32 cnt)
            (by rw [hmg]; rfl) (by simp [s₁, gval_setGlobal, h1]) ?_
          refine X.localGet (x := ⟨0⟩) (v := .i32 n) rfl ?_
          refine X.sub32 (us := []) ?_
          refine X.globalSet (s := s₁) (f := F) (us := []) (x := ⟨1⟩) (a := 1)
            (by rw [hmg]; rfl) (by simp [s₁, gval_setGlobal, h1]) ?_
          refine X.localGet (x := ⟨0⟩) (v := .i32 n) rfl ?_
          refine X.localGet (x := ⟨2⟩) (v := .i32 acc) rfl ?_
          refine X.return_ (hret _ _ [.i32 n, .i32 acc] (by rw [hgj]; rfl) fun v hv =>
            ⟨hpost n acc _ hacc (fun _ => by simp) v hv, ?_⟩)
          show ringInv (chunkNext (I := RI) ringPix g ⟨⟨1, hj⟩, ⟨[.i32 n], ht⟩⟩ v) _
          rw [hnext n acc v hv]
          simp only [chunkStep, hng, ↓reduceIte]
          refine ⟨by simp [s₁, hfs], (st + n) % 8, cnt - n, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp [s₁, gval_setGlobal, h0]
          · simp [s₁, gval_setGlobal, h1]
          · rw [hst']; exact hstl
          · rw [cnt_sub hnc, hcg]; simp
          · simp only [List.length_drop]; omega
          · simpa [s₁] using hml
          · intro k hk
            simp only [List.length_drop] at hk
            obtain ⟨mi, hmi, hl⟩ := hld (n.toNat + k) (by omega)
            refine ⟨mi, by simpa [s₁] using hmi, ?_⟩
            rw [hst', slot_shift, List.getElem_drop]
            exact hl
        · -- `i ≠ 0`: add the value `i - 1`
          have hi0' : i ≠ 0 := by simpa using bool32_eq_zero hi0
          obtain ⟨hip, hilt⟩ := i_pred hi0'
          have hipos : 0 < i.toNat := by omega
          have hig : i.toNat - 1 < g.length := by omega
          refine X.localGet (x := ⟨1⟩) (v := .i32 i) rfl ?_
          refine X.i32Const (us := [] ++ [.i32 i]) ?_
          refine X.add32 (us := []) ?_
          refine X.localSet (x := ⟨1⟩) (by exact (by decide : (1 : Nat) < 3)) ?_
          let i' := i + BitVec.allOnes 32
          let F : Frame := ⟨[some (.i32 n), some (.i32 i'), some (.i32 acc)], fi.module⟩
          refine X.globalGet (f := F) (us := []) (x := ⟨0⟩) (a := 0) (by rw [hmg]; rfl) h0 ?_
          refine X.localGet (x := ⟨1⟩) (v := .i32 i') rfl ?_
          refine X.add32 (us := []) ?_
          refine X.remu8 (us := []) ?_
          refine X.mul8 (us := []) ?_
          refine X.load64 (F := F) (us := []) hFm hml ((hTo F).1) fun mi c hmi hc => ?_
          obtain ⟨mi₀, hmi₀, hl₀⟩ := hld (i.toNat - 1) hig
          rw [hmi] at hmi₀
          cases hmi₀
          have hi'cap : i'.toNat < cap := by
            simp only [i', hip, cap]; simp only [cap] at hgc; omega
          rw [slot_addr hst hi'cap] at hc
          simp only [i', hip] at hc
          rw [hl₀] at hc
          cases hc
          refine X.wWordM hS hfs hm hTo fun a ha => ?_
          refine X.localGet (x := ⟨2⟩) (v := .i32 acc) rfl ?_
          refine X.wConsM hS hfs hm ha hacc hTo fun c hc => ?_
          refine X.localSet (x := ⟨2⟩) (by exact (by decide : (2 : Nat) < 3)) ?_
          refine X.br0 ⟨[], [], rfl, rfl, rfl, rfl, i', c, rfl, by simp only [i', hip]; omega, ?_⟩
          rw [hc]
          simp only [i', hip]
          have hgt : i.toNat ≤ (g.take n.toNat).length := by simp; omega
          rw [ofAtoms_drop_pred hipos hgt, List.getElem_take]

end Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.Ring
