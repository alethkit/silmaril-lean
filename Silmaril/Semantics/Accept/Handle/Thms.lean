module

public import Silmaril.Semantics.Accept.Handle.Defs
public import Silmaril.Semantics.Accept.Host.Thms
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Relation
import Silmaril.Proofs.Semantics.Accept.Handle.Writer
import Silmaril.Proofs.Semantics.Accept.Handle.Reader
import Silmaril.Proofs.Semantics.Accept.Handle.Node
import Silmaril.Proofs.Semantics.Accept.Handle.Hom

/-!
# Handle-based acceptance: laws

**Writers** (store semantics `writerLang`, fixed environments `fixedLang`):

* policy order: `writerLang_mono` (`Policy.Le`: `trap ≤ ignore ≤ ub` for invalid accepts,
  `trap ≤ fail ≤ ub` for invalid writes, no interning below interning);
* the fixed-environment chain, for policies without write UB:
  `writerLang W pol ⊆ fixedLang W {pol with onAccept := .ub} univ ⊆ writerLang W {… ub}`
  (`writerLang_subset_fixedLang`, `fixedLang_subset`): restricting the UB reading to a fixed
  environment agreeing with every allocation lies between `ignore` and the UB top;
* persistence: stores only grow along runs (`Run.store_extends`);
* capacity: without interning, successful handles are pairwise distinct
  (`successes_nodup`), so a run has at most `|{h | h ≠ sentinel}|` of them
  (`successes_length_le`; for `i32`, `2 ^ 32` or `2 ^ 32 - 1`);
* the constructed set: under a child relation of the signature, the language of
  `acceptAll`-only traces is downward closed (`writerLang_downClosed`);
* writer homomorphisms (`Writer.Hom`: operations along `f`, trees along an injective `g`,
  building commutes) transport languages: `writerLang_hom_subset`, and `writerLang_hom`
  (equality without undefined behaviour; UB accepts every tree of the target, not only the
  image);
* error-return accept: `writerLang_subset_eraseErr`, with equality for modules that ignore the
  returned status (`writerLang_eraseErr_eq`);
* sentinels: on traces that never receive the sentinel a sentinel policy *is* the policy
  without one (`writerLang_noRet`), hence accepts no more than it
  (`writerLang_noRet_subset`); renaming handles by a bijection moves the sentinel and preserves
  the language (`writerLang_rename`), so the sentinel `0` and the sentinel `-1` correspond by
  the swap `0 ↔ -1` of handle values (`writerLang_sentinel_swap`), not by numeric identity.
  A trace receiving the sentinel twice can accept more than any sentinel-free reading
  (`Examples`).

**Readers** (`readerLang` over an explicit set `Envs` of fixed environments):

* policy order: `readerLang_mono` (`trap ≤ dflt ≤ arbitrary ≤ ub`, accept policies by rank,
  environments by inclusion);
* correct reads: under the trapping read policy every answered read is correct
  (`trap_reads_correct`); with a default answer, a non-default answer is correct and with a
  typed error the default answer is exactly an invalid query (`error_iff_invalid`);
* **certified acceptance is sound** under the trapping read policy (`readerLang_trap_subset`).
  It is *not* sound under `arbitrary` (`Examples`), which is why arbitrary data and UB are
  different policies even though both may answer anything.

**Combined sessions**: every cut of a run splits it at a store that the rest of the run
extends (`combined_cut`); a successful write stores its tree (`combined_write`) and every read
answers from the current store (`combined_read`), so with a monotone reader a correct answer
stays correct for every later store (`Reader.Mono.persist`).

**Node environments**: unfoldings are functional (`unfold_functional`), a handle on a cycle
unfolds to nothing (`not_unfold_of_cycle`), and the realizing tree environment exists and is
unique (`realize_realizes`, `realizes_unique`).
-/

@[expose] public section

namespace Silmaril.Accept.Handle

open Silmaril.Accept.Host

universe u v w x

section Writer

variable {Op : Type u} {H : Type v} {X : Type w} [DecidableEq H] {W : Writer Op X}

theorem writerLang_mono {pol pol' : Policy H} (hle : pol.Le pol') (T : Set (List (WEv Op H))) :
    writerLang W pol T ⊆ writerLang W pol' T :=
  Silmaril.Proofs.Semantics.Accept.Handle.writerLang_mono hle T

theorem fixedLang_subset (pol : Policy H) (Envs : Set (Env H X)) (T : Set (List (WEv Op H))) :
    fixedLang W pol Envs T ⊆ writerLang W pol T :=
  Silmaril.Proofs.Semantics.Accept.Handle.fixedLang_subset pol Envs T

theorem writerLang_subset_fixedLang {pol : Policy H} (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) (T : Set (List (WEv Op H))) :
    writerLang W pol T ⊆ fixedLang W {pol with onAccept := .ub} Set.univ T :=
  Silmaril.Proofs.Semantics.Accept.Handle.writerLang_subset_fixedLang hw ha T

theorem Run.store_extends {pol : Policy H} {fix : Option (Env H X)} {s s' : WState H X}
    {t : List (WEv Op H)} {A : Set X} (hr : (writer W pol fix).Run s t s' A) :
    s.store.Extends s'.store :=
  Silmaril.Proofs.Semantics.Accept.Handle.run_extends hr

theorem mem_successes {pol : Policy H} {h : H} {t : List (WEv Op H)}
    (hm : h ∈ successes pol t) : pol.sentinel ≠ some h :=
  Silmaril.Proofs.Semantics.Accept.Handle.mem_successes hm

theorem successes_nodup {pol : Policy H} (hi : pol.intern = false) (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) {s' : WState H X} {t : List (WEv Op H)} {A : Set X}
    (hr : (writer W pol).Run WState.init t s' A) : (successes pol t).Nodup :=
  (Silmaril.Proofs.Semantics.Accept.Handle.successes_fresh hi hw ha hr
    (by simp [WState.init])).1

theorem successes_length_le [Fintype H] {pol : Policy H} (hi : pol.intern = false)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) {s' : WState H X}
    {t : List (WEv Op H)} {A : Set X} (hr : (writer W pol).Run WState.init t s' A) :
    (successes pol t).length ≤ (Finset.univ.filter fun h => pol.sentinel ≠ some h).card :=
  Silmaril.Proofs.Semantics.Accept.Handle.successes_length_le hi hw ha hr

theorem writerLang_downClosed {Sub : X → X → Prop} (hW : W.ChildRel Sub) {pol : Policy H}
    (hw : pol.onWrite ≠ .ub) {T : Set (List (WEv Op H))} (hT : ∀ t ∈ T, ∀ e ∈ t, AllOnly e) :
    DownClosed Sub (writerLang W pol T) :=
  Silmaril.Proofs.Semantics.Accept.Handle.writerLang_downClosed hW hw hT

theorem writerLang_subset_eraseErr {pol : Policy H} (ha : pol.onAccept ≠ .ub)
    (T : Set (List (WEv Op H))) :
    writerLang W pol T ⊆ writerLang W {pol with onAccept := .ignore} (List.map WEv.eraseErr '' T) :=
  Silmaril.Proofs.Semantics.Accept.Handle.writerLang_subset_eraseErr ha T

theorem writerLang_eraseErr_eq {pol : Policy H} (ha : pol.onAccept = .ignore)
    {T : Set (List (WEv Op H))} (hT : ResultOblivious T) :
    writerLang W pol (List.map WEv.eraseErr '' T) = writerLang W pol T :=
  Silmaril.Proofs.Semantics.Accept.Handle.writerLang_eraseErr_eq ha hT

theorem writerLang_noRet {pol : Policy H} {s : H} (hs : pol.sentinel = some s)
    {T : Set (List (WEv Op H))} (hT : ∀ t ∈ T, NoRet s t) :
    writerLang W pol T = writerLang W {pol with sentinel := none} T :=
  Silmaril.Proofs.Semantics.Accept.Handle.writerLang_noRet hs hT

/-- **A sentinel accepts no more than no sentinel**, on the traces where the sentinel is never
returned. -/
theorem writerLang_noRet_subset {pol : Policy H} {s : H} (hs : pol.sentinel = some s)
    (T : Set (List (WEv Op H))) :
    writerLang W pol (T ∩ {t | NoRet s t}) ⊆ writerLang W {pol with sentinel := none} T := by
  rw [writerLang_noRet (T := T ∩ {t | NoRet s t}) hs (fun t ht => ht.2)]
  exact Host.lang_mono Set.inter_subset_left

theorem writerLang_rename (π : H ≃ H) (pol : Policy H) (T : Set (List (WEv Op H))) :
    writerLang W (pol.rename π) (List.map (WEv.rename π) '' T) = writerLang W pol T :=
  Silmaril.Proofs.Semantics.Accept.Handle.writerLang_rename π pol T

/-- **Sentinel `0` versus sentinel `-1`** for `i32` handles: the languages correspond under the
swap of the two handle values. -/
theorem writerLang_sentinel_swap {Op' : Type u} {X' : Type w} {W' : Writer Op' X'}
    (pol : Policy (BitVec 32)) (hs : pol.sentinel = some 0) (T : Set (List (WEv Op' (BitVec 32)))) :
    writerLang W' {pol with sentinel := some (-1 : BitVec 32)}
      (List.map (WEv.rename (H := BitVec 32) (Equiv.swap (0 : BitVec 32) (-1 : BitVec 32))) '' T) =
      writerLang W' pol T := by
  have h := writerLang_rename (W := W') (Equiv.swap (0 : BitVec 32) (-1)) pol T
  have hp : pol.rename (Equiv.swap (0 : BitVec 32) (-1)) = {pol with sentinel := some (-1)} := by
    simp [Policy.rename, hs]
  rwa [hp] at h

/-- **Writer homomorphisms transport languages**: the image module accepts at least the image
of the language. -/
theorem writerLang_hom_subset {Op' : Type u} {X' : Type w} {W' : Writer Op' X'} {f : Op → Op'}
    {g : X → X'} (hW : W.Hom W' f g) (pol : Policy H) (T : Set (List (WEv Op H))) :
    g '' writerLang W pol T ⊆ writerLang W' pol (List.map (WEv.mapOp f) '' T) :=
  Silmaril.Proofs.Semantics.Accept.Handle.writerLang_hom_subset hW pol T

/-- Without undefined behaviour, exactly the image. -/
theorem writerLang_hom {Op' : Type u} {X' : Type w} {W' : Writer Op' X'} {f : Op → Op'}
    {g : X → X'} (hW : W.Hom W' f g) {pol : Policy H} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) (T : Set (List (WEv Op H))) :
    writerLang W' pol (List.map (WEv.mapOp f) '' T) = g '' writerLang W pol T :=
  Silmaril.Proofs.Semantics.Accept.Handle.writerLang_hom hW ha hw T

end Writer

section Reader

variable {Q : Type u} {A : Type v} {H : Type w} {X : Type x} {R : Reader Q A H X}

theorem readerLang_mono {pol pol' : OnBadRead Q A} (hle : OnBadRead.Le pol pol')
    {oa oa' : OnInvalid} (ha : oa.rank ≤ oa'.rank) {Envs Envs' : Set (Env H X)}
    (hE : Envs ⊆ Envs') (T : Set (List (REv Q A H))) :
    readerLang R pol oa Envs T ⊆ readerLang R pol' oa' Envs' T :=
  Silmaril.Proofs.Semantics.Accept.Handle.readerLang_mono hle ha hE T

theorem trap_reads_correct {oa : OnInvalid} (hoa : oa ≠ .ub) {ρ : Env H X} {p : Phase}
    {t : List (REv Q A H)} {S : Set X} (hr : (reader R .trap oa ρ).Run .live t p S) :
    ∀ qa ∈ REv.reads t, R.valid ρ qa.1 ∧ R.ok ρ qa.1 qa.2 :=
  (Silmaril.Proofs.Semantics.Accept.Handle.trap_facts hoa hr (by simp)).2

/-- Under the trapping read policy (and no accept UB) a run never reaches chaos. -/
theorem trap_not_chaos {oa : OnInvalid} (hoa : oa ≠ .ub) {ρ : Env H X} {p : Phase}
    {t : List (REv Q A H)} {S : Set X} (hr : (reader R .trap oa ρ).Run .live t p S) :
    p ≠ .chaos :=
  (Silmaril.Proofs.Semantics.Accept.Handle.trap_facts hoa hr (by simp)).1

theorem dflt_read {d : Q → A} {ρ : Env H X} {q : Q} {a : A} {S : Set A}
    (hS : answers R (.dflt d) ρ q = some S) (ha : a ∈ S) :
    (R.valid ρ q ∧ R.ok ρ q a) ∨ (¬ R.valid ρ q ∧ a = d q) :=
  Silmaril.Proofs.Semantics.Accept.Handle.dflt_read hS ha

theorem error_iff_invalid {d : Q → A} (hd : ErrorDisjoint R d) {ρ : Env H X} {q : Q} {a : A}
    {S : Set A} (hS : answers R (.dflt d) ρ q = some S) (ha : a ∈ S) :
    a = d q ↔ ¬ R.valid ρ q :=
  Silmaril.Proofs.Semantics.Accept.Handle.error_iff_invalid hd hS ha

theorem readerLang_trap_subset {oa : OnInvalid} (hoa : oa ≠ .ub)
    {cert : List (Q × A) → H → Prop} {L : Set X} (hc : CertSound R cert L)
    {T : Set (List (REv Q A H))} (hT : Certified cert T) (Envs : Set (Env H X)) :
    readerLang R .trap oa Envs T ⊆ L :=
  Silmaril.Proofs.Semantics.Accept.Handle.readerLang_trap_subset hoa hc hT Envs

end Reader

section Combined

variable {Op : Type u} {H : Type v} {X : Type w} [DecidableEq H] {Q : Type u} {A : Type u}
variable {W : Writer Op X} {R : Reader Q A H X} {pol : Policy H} {rpol : OnBadRead Q A}

theorem combined_cut {s s' : WState H X} {t u : List (CEv Op H Q A)} {S : Set X}
    (hr : (combined W R pol rpol).Run s (t ++ u) s' S) :
    ∃ m B C, (combined W R pol rpol).Run s t m B ∧ (combined W R pol rpol).Run m u s' C ∧
      s.store.Extends m.store ∧ m.store.Extends s'.store :=
  Silmaril.Proofs.Semantics.Accept.Handle.crun_cut hr

theorem combined_write {s s' : WState H X} {op : Op} {args : List H} {r : H} {S : Set X}
    (hs : CStep W R pol rpol s (.w (.write op args r)) s' S) (hr : pol.sentinel ≠ some r)
    (hl : s'.phase = .live) :
    ∃ t, W.built s.store op args = some t ∧ s'.store r = some t :=
  Silmaril.Proofs.Semantics.Accept.Handle.cstep_write hs hr hl

theorem combined_read {s s' : WState H X} {q : Q} {a : A} {S : Set X}
    (hs : CStep W R pol rpol s (.r q a) s' S) (hl : s'.phase = .live) :
    ∃ S', answers R rpol s.store q = some S' ∧ a ∈ S' :=
  Silmaril.Proofs.Semantics.Accept.Handle.cstep_read hs hl

/-- **Consistency with every future read**: in a run `u ++ write ++ v ++ read ++ w`, the
written handle keeps its tree in the store the read is answered from. -/
theorem combined_write_read {s s' : WState H X} {u v w : List (CEv Op H Q A)} {op : Op}
    {args : List H} {r : H} {q : Q} {a : A} {S : Set X} (hr : pol.sentinel ≠ some r)
    (hrun : (combined W R pol rpol).Run s (u ++ CEv.w (.write op args r) :: (v ++ CEv.r q a :: w))
      s' S) :
    ∃ sw sw' sr sr' : WState H X, (sw'.phase = .live → ∃ t, W.built sw.store op args = some t ∧
        sw'.store r = some t) ∧ sw'.store.Extends sr.store ∧
      (sr'.phase = .live → ∃ S', answers R rpol sr.store q = some S' ∧ a ∈ S') := by
  have hc := combined_cut (t := u) hrun
  obtain ⟨sw, B, C, _, h2, _, _⟩ := hc
  have hc2 := Host.Run.append_inv (h := combined W R pol rpol)
    (t := [CEv.w (.write op args r)]) (u := v ++ CEv.r q a :: w) h2
  obtain ⟨sw', B', C', hw, hrest, _⟩ := hc2
  cases hw with
  | cons hs hnil =>
      cases hnil
      have hc3 := combined_cut (t := v) hrest
      obtain ⟨sr, _, _, _, h4, hext, _⟩ := hc3
      cases h4 with
      | cons hs' _ =>
          exact ⟨sw, sw', sr, _, fun hl => combined_write hs hr (by simpa using hl), hext,
            fun hl => combined_read hs' hl⟩

omit [DecidableEq H] in
/-- With a monotone reader, a correct answer stays correct in every extension of the store. -/
theorem Reader.Mono.persist (hM : R.Mono) {σ σ' : Env H X} (hext : σ.Extends σ') {q : Q} {a : A}
    (hv : R.valid σ q) (hok : R.ok σ q a) : R.valid σ' q ∧ R.ok σ' q a :=
  ⟨hM.1 hext hv, hM.2 hext hv hok⟩

end Combined

section Node

variable {H : Type u} {N : Type v} {X : Type w} {mk : N → List X → Option X} {ν : NodeEnv H N}

theorem unfold_functional {h : H} {x y : X} (hx : Unfold mk ν h x) (hy : Unfold mk ν h y) :
    x = y :=
  Silmaril.Proofs.Semantics.Accept.Handle.unfold_functional hx hy

theorem not_unfold_of_cycle {size : X → Nat}
    (hsize : ∀ ⦃m xs x⦄, mk m xs = some x → ∀ c ∈ xs, size c < size x) {h : H}
    (hc : Relation.TransGen ν.Child h h) (x : X) : ¬ Unfold mk ν h x :=
  Silmaril.Proofs.Semantics.Accept.Handle.not_unfold_of_cycle hsize hc x

theorem realize_realizes : Realizes mk ν (realize mk ν) :=
  Silmaril.Proofs.Semantics.Accept.Handle.realize_realizes

theorem realizes_unique {ρ ρ' : Env H X} (h : Realizes mk ν ρ) (h' : Realizes mk ν ρ') :
    ρ = ρ' :=
  Silmaril.Proofs.Semantics.Accept.Handle.realizes_unique h h'

end Node

end Silmaril.Accept.Handle
