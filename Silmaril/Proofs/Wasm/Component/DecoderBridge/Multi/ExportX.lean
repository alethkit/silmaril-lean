module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.ComposeX

/-!
# The export call from the invariant, in pieces

`exportRefX_of`: **`Task.exportRefX` from `Task.exportIR`, `Task.coreRunShared` and
`Task.callLift`**. From `NodesInv`: the reading's first export is the reference scope's first
export (`FrameRelX.exports`), the option-less lift of the core function at `a`
(`FuncRelS`), export `i` of the core instance `k` of the reading (`EnvAddr`). The IR's export phase
names the same core instance as node `j`, whose core instance is the relocated module instance
(`NodeAt`), so `a` is the relocated address of the IR's function (`lookup_exports_minst`); its run
is a run in the shared core store (`Task.coreRunShared`), and the session call wraps it
(`Task.callLift`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Conformance Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstTests Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Reference.Core3Adder (first)
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp
open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Instantiate
open Silmaril.Wasm.SingleThreaded (profile neverFail)

theorem lookup_map_addr (h : Silmaril.Wasm.Execution.Core.ExternAddr →
      Silmaril.Wasm.Execution.Core.ExternAddr) (nm : String) :
    ∀ l : List Silmaril.Wasm.Execution.Core.ExportInst,
      (l.map fun x => (x.name, h x.addr)).lookup nm =
        ((l.map fun x => (x.name, x.addr)).lookup nm).map h
  | [] => rfl
  | x :: l => by
    cases hb : nm == x.name <;> simp [List.lookup_cons, hb, lookup_map_addr h nm l]

theorem lookup_xinst (δ : GShift) (nm : String) (l : List Silmaril.Wasm.Execution.Core.ExportInst) :
    ((l.map δ.xinst).map fun x => (x.name, x.addr)).lookup nm =
      ((l.map fun x => (x.name, x.addr)).lookup nm).map δ.xa := by
  rw [List.map_map]
  exact lookup_map_addr δ.xa nm l

/-- The relocated module instance exports the relocated addresses. -/
theorem lookup_exports_minst (δ : GShift) (mi : Silmaril.Wasm.Execution.Core.ModuleInst)
    (nm : String) :
    ((core3 neverFail).exports (δ.minst mi)).lookup nm = ((irEng.exports mi).lookup nm).map δ.xa :=
  lookup_xinst δ nm mi.exports

theorem instsVal_length (l : List (List (String × Nat))) : (instsVal l).length = l.length := by
  simp [instsVal]

theorem forall₂_getElem? {α β : Type} {P : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ P l₁ l₂ → ∀ {j : Nat} {a : α}, l₁[j]? = some a →
      ∃ b, l₂[j]? = some b ∧ P a b
  | _, _, .nil, _, _, h => by cases h
  | _ :: _, _ :: _, .cons hp _, 0, _, h => by cases h; exact ⟨_, rfl, hp⟩
  | _ :: _, _ :: _, .cons _ hr, j + 1, _, h => forall₂_getElem? hr h

theorem forall₂_getElem?_left {α β : Type} {P : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ P l₁ l₂ → ∀ {j : Nat} {b : β}, l₂[j]? = some b →
      ∃ a, l₁[j]? = some a ∧ P a b
  | _, _, .nil, _, _, h => by cases h
  | _ :: _, _ :: _, .cons hp _, 0, _, h => by cases h; exact ⟨_, rfl, hp⟩
  | _ :: _, _ :: _, .cons _ hr, j + 1, _, h => forall₂_getElem?_left hr h

/-- **The export call from the invariant, from its three pieces.** -/
theorem exportRefX_of (hA : Task.exportIR) (hB : Task.coreRunShared) (hC : Task.callLift) :
    Task.exportRefX := by
  intro b c r ps xs n ws M inst es hpc hr hv hf himp hnodes hex hu hxs hp hN
  obtain ⟨R, e, hR, hhead, hall⟩ := hA b c r ps xs n ws hpc hr hv hf himp hnodes hex hu hxs hp
  obtain ⟨R', sc, pre, mi, cargs, post, esN, hR', hs, hes, hF, hci, hNA⟩ := hN.frame
  rw [hR] at hR'
  cases hR'
  -- the first export of the scope
  obtain ⟨x0, xr, hx⟩ : ∃ x0 xr, R.exports = x0 :: xr := by
    cases h : R.exports with
    | nil => rw [h] at hhead; cases hhead
    | cons x0 xr => exact ⟨x0, xr, rfl⟩
  rw [hx] at hhead
  simp only [List.head?_cons, Option.some.injEq] at hhead
  subst hhead
  have hE := hF.exports
  rw [hx] at hE
  obtain ⟨y0, yr, ⟨fid, rfl, hfr⟩, -, hy⟩ := List.forall₂_cons_left_iff.mp hE
  have hl : es.lookup n = some fid := by
    rw [hes, hy]
    simp [funcExports]
  obtain ⟨a, ty, hfun, hty, henv, -⟩ := hfr getTy e rfl
  obtain ⟨k, base, i, exps, esk, nm, cft, hk, hek, hi, he, hlk⟩ := henv
  obtain ⟨j, x, ai, c', v, rfl, hxj, hai, hrun, hst, rfl⟩ :=
    hall pre mi cargs post k base i exps nm cft hs hk hi he
  -- node `j`'s core instance
  rw [hci, List.getElem?_append_right (by rw [instsVal_length]; omega), instsVal_length,
    Nat.add_sub_cancel_left] at hek
  obtain ⟨esj, hesj, hat⟩ := forall₂_getElem? hNA hxj
  rw [hek] at hesj
  cases hesj
  obtain ⟨g, hP, ⟨U, hU⟩, rfl⟩ := hat
  have e := lookup_exports_minst g.sh x.minst nm
  rw [hai] at e
  have hlk' : (Option.some (g.sh.xa (.func ai)) : Option Silmaril.Wasm.Execution.Core.ExternAddr) =
      some (.func a) := e.symm.trans hlk
  simp only [Option.some.injEq] at hlk'
  have ha : a = g.fnMap ai := by
    simp only [GShift.xa, Gap.sh] at hlk'
    cases hlk'
    rfl
  subst ha
  obtain ⟨p, hpj, -⟩ := forall₂_getElem?_left hxs hxj
  obtain ⟨y, hy₁, hy₂⟩ := hB b c r ps xs j p x g U nm ai c' _ hpc hr hf himp hnodes hxs hpj hxj
    hP hai hrun hst
  rw [← hU] at hy₁
  obtain ⟨ι, hι, hok⟩ := hN.insts
  obtain ⟨M', hS, hh⟩ := hC M fid (g.fnMap ai) ty y v hN.ctl hN.lock ⟨ι, hι, hok⟩ hN.calls.1
    hN.calls.2 hfun hty hy₁ hy₂
  exact ⟨fid, M', hl, hS, hh⟩

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi
