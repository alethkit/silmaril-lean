module

public import Silmaril.Wasm.Component.DecoderBridge.MultiX.Defs
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.IR
public import Silmaril.Proofs.Wasm.Component.InstSem.WiredExport

/-!
# The IR's export phase (`Task.exportIR`)

* **The reading's layout** (`refRead_layout`): after the inline core instances of the definitions
  before the first core instantiation, the reading's core instances are the nodes', each at its
  base in the environment (after the imports and the exports of the nodes before it);
* **the IR's export call** (`InstSem.denI_ex_node`): the first export, the option-less lift of
  environment function `e`, makes one call of `e`; the call is answered by the node owning `e`,
  after its instantiation, without calls below;
* **the node's run** (`InstSem.engineI_ex_inv`): the node's engine instance runs its start
  function, then the export from the store it leaves; the export's run makes no import call
  (`exportRun_nil`: an import call of a typed run has one `i32` argument, so the wiring `lowF`
  calls `f`, a call below);
* **`exportIR`**: `Task.exportIR`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Conformance Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Proofs.Wasm.Component.InstSem
open Silmaril.Proofs.Wasm.Component.DecoderBridge (RDef)
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore
open Silmaril.Wasm.SingleThreaded (Internal status neverFail profile)

/-! ## The reading's layout -/

/-- The number of function exports `coreIface` reads off a module (`0` outside the fragment). -/
def ifaceWidth (m : Silmaril.Wasm.Module) : Nat :=
  match coreIface m with
  | .ok (_, _, e) => e.length
  | .error _ => 0

/-- **The nodes' core instances in the environment**: from `e₀`, each node's instance is at the
base its predecessors leave, with the exports `coreIface` reads off its module. -/
inductive Layout : Nat → List RCI → List (Silmaril.Wasm.Module × List Impl) → Nat → Prop
  | nil (e : Nat) : Layout e [] [] e
  | snoc {e₀ e : Nat} {cis : List RCI} {ns : List (Silmaril.Wasm.Module × List Impl)}
      {m : Silmaril.Wasm.Module} {w : List Impl} {nm : List (String × String)} {im exps : CoreIface} :
      Layout e₀ cis ns e → coreIface m = .ok (nm, im, exps) →
      Layout e₀ (cis ++ [.node e exps]) (ns ++ [(m, w)]) (e + exps.length)

theorem Layout.len {e₀ e : Nat} {cis : List RCI} {ns : List (Silmaril.Wasm.Module × List Impl)}
    (h : Layout e₀ cis ns e) :
    cis.length = ns.length ∧ e = e₀ + (ns.map fun q => ifaceWidth q.1).sum := by
  induction h with
  | nil => exact ⟨rfl, by simp⟩
  | snoc _ hc ih =>
    refine ⟨by simp [ih.1], ?_⟩
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
      List.sum_nil, ifaceWidth, hc, ih.2]
    omega

theorem Layout.get {e₀ e : Nat} {cis : List RCI} {ns : List (Silmaril.Wasm.Module × List Impl)}
    (h : Layout e₀ cis ns e) {k base : Nat} {exps : CoreIface}
    (hk : cis[k]? = some (.node base exps)) :
    ∃ m w nm im, ns[k]? = some (m, w) ∧ coreIface m = .ok (nm, im, exps) ∧
      base = e₀ + ((ns.take k).map fun q => ifaceWidth q.1).sum := by
  induction h with
  | nil => cases hk
  | @snoc e cis ns m w nm im exps' hL hc ih =>
    have hl := hL.len
    by_cases hlt : k < cis.length
    · rw [List.getElem?_append_left hlt] at hk
      obtain ⟨m', w', nm', im', h1, h2, h3⟩ := ih hk
      refine ⟨m', w', nm', im', ?_, h2, ?_⟩
      · rw [List.getElem?_append_left (by omega), h1]
      · rw [List.take_append_of_le_length (by omega), h3]
    · rw [List.getElem?_append_right (by omega)] at hk
      have hk' : k = cis.length := by
        rcases Nat.lt_or_ge k (cis.length + 1) with h' | h'
        · omega
        · rw [List.getElem?_eq_none (by simp; omega)] at hk; cases hk
      subst hk'
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq, RCI.node.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      refine ⟨m, w, nm, im, ?_, hc, ?_⟩
      · rw [List.getElem?_append_right (by omega), hl.1]; simp
      · rw [hl.1, List.take_left' rfl, hl.2]

/-- The invariant of the reading after the first core instantiation: the core instances are the
first `A` followed by the nodes', laid out from `e₀`. -/
def LayInv (e₀ : Nat) (A : List RCI) (R : RSt) : Prop :=
  ∃ cis, R.coreInsts = A ++ cis ∧ Layout e₀ cis R.nodes R.env

theorem refStep_layInv {e₀ : Nat} {A : List RCI} {R R' : RSt} {d : RDef}
    (hd : ∀ its, d ≠ .coreInstance (.exports its)) (h : refStep R d = some R')
    (hI : LayInv e₀ A R) : LayInv e₀ A R' := by
  obtain ⟨cis, hc, hl⟩ := hI
  unfold refStep at h
  split at h
  all_goals first
    | (cases h; exact ⟨cis, hc, hl⟩)
    | exact absurd rfl (hd _)
    | cases h
    | (simp only [bind, Option.bind_eq_some_iff] at h)
  case h_4 =>
    obtain ⟨m, -, ⟨names, im, exps⟩, hci, w, -, h⟩ := h
    cases h
    have hci' : coreIface m = .ok (names, im, exps) := by
      cases hc' : coreIface m with
      | error e => rw [hc'] at hci; cases hci
      | ok v => rw [hc'] at hci; cases hci; rfl
    exact ⟨cis ++ [.node R.env exps], by simp [hc], .snoc hl hci'⟩
  all_goals (unfold LayInv; aesop)

theorem foldlM_layInv {e₀ : Nat} {A : List RCI} :
    ∀ {ds : List RDef} {R R' : RSt}, (∀ d ∈ ds, ∀ its, d ≠ .coreInstance (.exports its)) →
      ds.foldlM refStep R = some R' → LayInv e₀ A R → LayInv e₀ A R'
  | [], R, R', _, h, hI => by simp at h; subst h; exact hI
  | d :: ds, R, R', hd, h, hI => by
    simp only [List.foldlM_cons, bind, Option.bind] at h
    cases hR : refStep R d with
    | none => simp [hR] at h
    | some R1 =>
      simp only [hR] at h
      exact foldlM_layInv (fun d' h' => hd d' (.tail _ h')) h
        (refStep_layInv (hd d (.head _)) hR hI)

theorem refStep_pre {R R' : RSt} {d : RDef} (hd : ¬ IsInst d) (h : refStep R d = some R') :
    R'.nodes = R.nodes ∧ R'.env = R.env ∧
      R'.coreInsts.length = R.coreInsts.length + (preInsts [d]).length := by
  unfold refStep at h
  split at h
  all_goals first
    | (cases h; simp [preInsts])
    | exact absurd trivial hd
    | cases h
    | (simp only [bind, Option.bind_eq_some_iff] at h)
  all_goals aesop (add norm preInsts)

theorem foldlM_pre :
    ∀ {ds : List RDef} {R R' : RSt}, (∀ d ∈ ds, ¬ IsInst d) → ds.foldlM refStep R = some R' →
      R'.nodes = R.nodes ∧ R'.env = R.env ∧
        R'.coreInsts.length = R.coreInsts.length + (preInsts ds).length
  | [], R, R', _, h => by simp at h; subst h; simp [preInsts]
  | d :: ds, R, R', hd, h => by
    simp only [List.foldlM_cons, bind, Option.bind] at h
    cases hR : refStep R d with
    | none => simp [hR] at h
    | some R1 =>
      simp only [hR] at h
      obtain ⟨h1, h2, h3⟩ := refStep_pre (hd d (.head _)) hR
      obtain ⟨h1', h2', h3'⟩ := foldlM_pre (fun d' h' => hd d' (.tail _ h')) h
      have hp : (preInsts (d :: ds)).length = (preInsts [d]).length + (preInsts ds).length := by
        cases d with
        | coreInstance ci => cases ci <;> simp [preInsts, Nat.add_comm]
        | _ => simp [preInsts]
      refine ⟨h1'.trans h1, h2'.trans h2, ?_⟩
      rw [h3', h3, hp]
      omega

theorem refStep_imports_len {R R' : RSt} {d : RDef} (h : refStep R d = some R') :
    R'.imports.length = R.imports.length + (if isFuncImport d then 1 else 0) := by
  unfold refStep at h
  split at h
  all_goals first
    | (cases h; simp [isFuncImport])
    | cases h
    | (simp only [bind, Option.bind_eq_some_iff] at h)
  all_goals aesop (add norm isFuncImport)

theorem foldlM_imports_len :
    ∀ {ds : List RDef} {R R' : RSt}, ds.foldlM refStep R = some R' →
      R'.imports.length = R.imports.length + (ds.filter isFuncImport).length
  | [], R, R', h => by simp at h; subst h; simp
  | d :: ds, R, R', h => by
    simp only [List.foldlM_cons, bind, Option.bind] at h
    cases hR : refStep R d with
    | none => simp [hR] at h
    | some R1 =>
      simp only [hR] at h
      rw [foldlM_imports_len h, refStep_imports_len hR, List.filter_cons]
      split
      · simp; omega
      · simp

/-- **The reading's layout**: the reading's imports are the component's function imports; its core
instances are the inline instances of the definitions before the first core instantiation,
followed by the nodes', laid out from the imports. -/
theorem refRead_layout {r : RefComponent} {R : RSt} {pre : List RDef} {mi : Nat}
    {cargs : List (String × Nat)} {post : List RDef} (hR : refRead r = some R)
    (hfc : firstCore? r = some (pre, mi, cargs, post))
    (hpost : ∀ d ∈ post, ∀ its, d ≠ .coreInstance (.exports its)) :
    R.imports.length = (r.filter isFuncImport).length ∧
      ∃ A : List RCI, A.length = (preInsts pre).length ∧ LayInv R.imports.length A R := by
  have hi := foldlM_imports_len hR
  simp only at hi
  refine ⟨by simpa using hi, ?_⟩
  have hnoI := firstCore?_noInst r hfc
  have hs := firstCore?_eq r hfc
  subst hs
  unfold refRead at hR
  rw [List.foldlM_append] at hR
  simp only [bind, Option.bind_eq_some_iff, List.foldlM_cons] at hR
  obtain ⟨R₁, h₁, R₂, h₂, hR⟩ := hR
  obtain ⟨hn₁, he₁, hc₁⟩ := foldlM_pre hnoI h₁
  simp only [refStep, bind, Option.bind_eq_some_iff] at h₂
  obtain ⟨m, -, ⟨names, im, exps⟩, hci, w, -, h₂⟩ := h₂
  injection h₂ with h₂
  have hci' : coreIface m = .ok (names, im, exps) := by
    cases hc' : coreIface m with
    | error e => rw [hc'] at hci; cases hci
    | ok v => rw [hc'] at hci; cases hci; rfl
  refine ⟨R₁.coreInsts, by simpa using hc₁, ?_⟩
  have hI : LayInv R₁.env R₁.coreInsts R₂ := by
    subst h₂
    refine ⟨[.node R₁.env exps], rfl, ?_⟩
    simp only [hn₁]
    exact .snoc (cis := []) (ns := []) (.nil _) hci'
  have := foldlM_layInv hpost hR hI
  rw [he₁] at this
  simpa [hi] using this

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi
