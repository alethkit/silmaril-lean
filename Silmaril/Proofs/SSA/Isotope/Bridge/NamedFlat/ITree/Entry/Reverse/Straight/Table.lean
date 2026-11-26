module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.Straight.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Straight.Body
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Straight

open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat Silmaril.Isotope.Bridge.NamedFlat.Entry
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Straight
open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG.Cyclic
open LambdaSSA (FiniteCFG Flat)
open LambdaSSA.Semantics.Interaction.Typed.Ordered

universe u v

private theorem term_readback {V K : Type u} {F : Type v} (tail : CFG.Term V K F) :
    CFG.Term.ofRegion? tail.toRegion = some tail := by
  induction tail <;> simp [CFG.Term.ofRegion?, CFG.Term.toRegion, *]

private theorem body_readback {V K : Type u} {F : Type v} (src : CFG.Body V K F) :
    CFG.Body.ofRegion? src.toRegion = some src := by
  induction src with
  | let1 | let2 => simp [CFG.Body.ofRegion?, CFG.Body.toRegion, *]
  | term tail => cases tail <;> simp [CFG.Body.toRegion, CFG.Body.ofRegion?, CFG.Term.toRegion,
      CFG.Term.ofRegion?, term_readback]

private theorem unpack_empty {V K : Type u} {F : Type v} (src : V × Nat) (d : Nat)
    (body : CFG.Body (V × Nat) K F) : Versioning.unpackBody [] src d body = body :=
  Option.get_of_eq_some _ (body_readback body)

private theorem lookup_index {K : Type u} {A : Type v} [BEq K] (items : List (K × A)) (label : K) :
    items.lookup label = (items.findFinIdx? (fun item => label == item.1)).map
      (fun i => items[i].2) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    rcases item with ⟨key, entry⟩
    simp only [List.lookup_cons, List.findFinIdx?_cons]
    cases label == key <;> simp [ih, Function.comp_def]

variable {Base V K : Type u} {F : Type v} [DecidableEq V] [DecidableEq K]

private theorem routes_empty (graph : CFG V K F) (exits : List K)
    (R : Fin (Versioning.compile graph).blocks.length → Ty Base) (D : Fin exits.length → Ty Base)
    (empty : ∀ i : Fin graph.blocks.length, Versioning.slots graph graph.blocks[i].2 = []) :
    Routes (labelIndex (Versioning.compile graph).blocks exits) (Versioning.destinations graph)
      (SSA.FiniteSum.append R D) (SSA.FiniteSum.append (fun i => .product (R i) .unit) D) := by
  intro label i numbered
  let compiled := Versioning.compile graph
  have order : (compiled.blocks.findFinIdx? (fun item => label == item.1)).map Fin.val =
      (graph.blocks.findFinIdx? (fun item => label == item.1)).map Fin.val := by
    simp [← List.findIdx?_eq_map_findFinIdx?_val, compiled, Versioning.compile, Function.comp_def]
  change labelIndex compiled.blocks exits label = some i at numbered
  cases hCompiled : compiled.blocks.findFinIdx? (fun item => label == item.1) with
  | none =>
    cases hSource : graph.blocks.findFinIdx? (fun item => label == item.1) with
    | some j => simp [hCompiled, hSource] at order
    | none =>
      simp only [labelIndex, hCompiled, Option.map_eq_some_iff] at numbered
      obtain ⟨j, _, rfl⟩ := numbered
      refine Or.inl ⟨?_, ?_⟩
      · rw [Versioning.destinations, lookup_index, hSource]
        rfl
      · rw [SSA.FiniteSum.append_right, SSA.FiniteSum.append_right]
  | some k =>
    cases hSource : graph.blocks.findFinIdx? (fun item => label == item.1) with
    | none => simp [hCompiled, hSource] at order
    | some j =>
      simp only [labelIndex, hCompiled, Option.some.injEq] at numbered
      subst i
      refine Or.inr ⟨?_, ?_⟩
      · rw [Versioning.destinations, lookup_index, hSource]
        exact congrArg some (empty j)
      · rw [SSA.FiniteSum.append_left, SSA.FiniteSum.append_left]

private theorem tabulate_checked {A : Type u} {count : Nat}
    {f : Fin count → Option A} {p : Fin count → A → Prop}
    (each : ∀ i, ∃ out, f i = some out ∧ p i out) :
    ∃ table, tabulate count f = some table ∧ ∀ i, p i (table i) := by
  induction count with
  | zero => exact ⟨Fin.elim0, rfl, fun i => i.elim0⟩
  | succ count ih =>
    obtain ⟨first, hFirst, pFirst⟩ := each 0
    obtain ⟨tail, hTail, pTail⟩ := ih (fun i => each i.succ)
    exact ⟨Fin.cases first tail, by simp [tabulate, hFirst, hTail],
      fun i => Fin.cases pFirst pTail i⟩

omit [DecidableEq K] in
private theorem checked_source [DecidableEq Base] [HasTy F (Ty Base)]
    {n labels : Nat} {index : K → Option (Fin labels)} {types : Fin labels → Ty Base}
    {names : Names V n} {ctx : BoundCtx (Ty Base) n} {src : CFG.Body V K F}
    (checks : sourceCheck index types names ctx src = true) :
    bodySupported src = true ∧ ∃ flat, body index names src = some flat ∧ checkBody types ctx flat = true := by
  cases found : body index names src <;> simp_all [sourceCheck]

omit [DecidableEq K] in
private theorem entry_scope {n : Nat} (captures : Fin n → V) (ctx : BoundCtx (Ty Base) n) :
    Scope (fun _ => 0) (first captures) ctx (first (fun i => (captures i, 0))) ctx := by
  intro reg i found
  exact ⟨i, by simpa [first] using found, rfl⟩

omit [DecidableEq K] in
private theorem block_scope {n : Nat} (reg : V) (ctx : BoundCtx (Ty Base) n) (A : Ty Base) :
    Scope (Version.setv (fun _ => 0) reg 1) (blockNames reg) (.snoc ctx A)
      (bindName (bindName (blockNames (n := n) (reg, 0)) (reg, 1)) (reg, 2))
      (.snoc (.snoc (.snoc ctx (.product A .unit)) A) .unit) := by
  intro x i found
  by_cases same : x = reg
  · subst x
    have eq : i = 0 := by simpa [blockNames, bindName] using found.symm
    subst i
    exact ⟨(0 : Fin (n + 2)).succ, by simp [Version.setv, bindName], rfl⟩
  · simp [blockNames, bindName, same] at found

private theorem block_checked [DecidableEq Base] [HasTy F (Ty Base)]
    {n labels : Nat} (graph : CFG V K F) (src : CFG.Block V K F)
    (index : K → Option (Fin labels)) (old new : Fin labels → Ty Base)
    (routes : Routes index (Versioning.destinations graph) old new)
    (ctx : BoundCtx (Ty Base) n) (A : Ty Base)
    (empty : Versioning.slots graph src = [])
    (checked : sourceCheck index old (blockNames src.param) (.snoc ctx A) src.body = true) :
    ∃ flat, body index (blockNames (Versioning.compileBlock graph src).param)
      (Versioning.compileBlock graph src).body = some flat ∧
      checkBody new (.snoc ctx (.product A .unit)) flat = true := by
  obtain ⟨supported, _, read, typed⟩ := checked_source checked
  obtain ⟨inside, hInside, tInside⟩ := version_body index _ old new routes
    (Versioning.registers graph) src.body supported 2 _ _ _ _ _
    (block_scope src.param ctx A) read typed
  refine ⟨.let₂ (.bv 0) inside, ?_, ?_⟩
  · simp [Versioning.compileBlock, empty, unpack_empty, Versioning.blockVersions, Version.unpackCur,
      body, operand, value, blockNames, bindName]
    exact hInside
  · simpa [checkBody, infer, BoundCtx.get] using tInside

variable {κ Label : Type (u + 1)} [DecidableEq Label] [DecidableEq κ]
  {n blocks : Nat} {P : FlatInstitution.Signature.{u, v} κ}
  {context : BoundCtx (Ty κ) n} {exits : List Label} {external : Fin exits.length → Ty κ}
  {fields : Label → List (Register × Ty κ)}
  {code : FiniteCFG P.Instr blocks exits.length n}

variable (a : Lowered (numberedInterface context exits external) fields code)

local notation "attached" => withLiveOut (P := P) fields a.source
local notation "versioned" => Versioning.compile attached
local notation "exitTypes" => Interface.external
  (LiveOut.exitInterface (numberedInterface context exits external) fields)

omit [DecidableEq κ] in
private theorem packetProfile_empty (R : Fin blocks → Ty κ) (saved : a.SavesCaptures)
    (empty : ∀ i, a.savedRegisters i = []) (i : Fin (versioned).blocks.length) :
    a.packetProfile R saved i = .product (R (Fin.cast a.reversionCount i)) .unit := by
  let members := (a.savedRegisters i).attach
  have nil : members = [] := List.eq_nil_of_length_eq_zero (by simp [members, empty i])
  change Ty.product _ (LiveOut.recordType (members.map _)) = _
  rw [nil]
  rfl

set_option maxHeartbeats 400000 in
theorem compiled_success (R : Fin blocks → Ty κ) (saved : a.SavesCaptures)
    (empty : ∀ i, a.savedRegisters i = []) (checked : checks a R = true) :
    ∃ table, compile attached exits (fun i : Fin n => (⟨i.val⟩ : Register)) = some table ∧
      let new := SSA.FiniteSum.append (a.packetProfile R saved) exitTypes
      checkBody new context table.entry = true ∧
        ∀ i, checkBody new (.snoc context (a.packetProfile R saved i)) (table.block i) = true := by
  let index := labelIndex (versioned).blocks exits
  let captures : Fin n → Register := fun i => ⟨i.val⟩
  let original := fun i => R (Fin.cast a.reversionCount i)
  let expanded := fun i => Ty.product (original i) .unit
  have profile : a.packetProfile R saved = expanded := funext (packetProfile_empty a R saved empty)
  rw [profile]
  let old := SSA.FiniteSum.append original exitTypes
  let new := SSA.FiniteSum.append expanded exitTypes
  have slotsEmpty (i : Fin (attached).blocks.length) :
      Versioning.slots attached (attached).blocks[i].2 = [] :=
    empty (Fin.cast (List.length_map _).symm i)
  have route := routes_empty attached exits original exitTypes slotsEmpty
  obtain ⟨sourceEntry, sourceBlocks⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨supported, _, read, typed⟩ := checked_source sourceEntry
  obtain ⟨entry, hEntry, tEntry⟩ := version_body index _ old new route (Versioning.registers attached)
    (attached).entry supported 0 (fun _ => 0) _ _ _ _ (entry_scope captures context) read typed
  have byBlock (i : Fin (versioned).blocks.length) :
      ∃ flat, body index (blockNames ((versioned).blocks[i].2.param)) (versioned).blocks[i].2.body = some flat ∧
        checkBody new (.snoc context (expanded i)) flat = true := by
    let j : Fin (attached).blocks.length := Fin.cast (List.length_map _) i
    have checkAt := List.all_eq_true.mp sourceBlocks i (by simp)
    have row : (versioned).blocks[i].2 = Versioning.compileBlock attached (attached).blocks[j].2 := by
      exact congrArg Prod.snd (List.getElem_map
        (fun item => (item.1, Versioning.compileBlock attached item.2))
        (l := (attached).blocks) (i := i.val) (h := by
          rw [List.length_map]
          exact j.isLt))
    rw [row]
    exact block_checked attached (attached).blocks[j].2 index old new route
      context (original i) (slotsEmpty j) checkAt
  obtain ⟨rows, hRows, tRows⟩ := tabulate_checked byBlock
  exact ⟨⟨entry, rows⟩, by
    unfold compile elaborate
    change (body index (first fun i => (captures i, 0)) (versioned).entry).bind
      (fun outgoing => (tabulate (versioned).blocks.length
        (fun i => body index (blockNames (versioned).blocks[i].2.param)
          (versioned).blocks[i].2.body)).map (FiniteCFG.mk outgoing)) = some (FiniteCFG.mk entry rows)
    rw [show body index (first fun i => (captures i, 0)) (versioned).entry = some entry from hEntry]
    exact congrArg (Option.map (FiniteCFG.mk entry)) hRows, tEntry, tRows⟩

theorem compiled_get_checks (R : Fin blocks → Ty κ) (saved : a.SavesCaptures)
    (empty : ∀ i, a.savedRegisters i = []) (checked : checks a R = true)
    (found : (compile attached exits (fun i : Fin n => (⟨i.val⟩ : Register))).isSome) :
    let table := (compile attached exits (fun i : Fin n => (⟨i.val⟩ : Register))).get found
    let new := SSA.FiniteSum.append (a.packetProfile R saved) exitTypes
    checkBody new context table.entry = true ∧
      ∀ i, checkBody new (.snoc context (a.packetProfile R saved i)) (table.block i) = true := by
  obtain ⟨_, read, typed⟩ := compiled_success a R saved empty checked
  simpa only [Option.get_of_eq_some found read] using typed

omit [DecidableEq κ] in
theorem empty_of_no_captures (closed : n = 0) (saved : a.SavesCaptures) :
    ∀ i, a.savedRegisters i = [] := by
  intro i
  cases shape : a.savedRegisters i with
  | nil => rfl
  | cons r rs =>
    have bound := saved i r (by simp [shape])
    omega

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Straight
