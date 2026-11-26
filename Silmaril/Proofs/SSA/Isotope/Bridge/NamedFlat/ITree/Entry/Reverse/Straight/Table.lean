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

private theorem unpack_one {V K : Type u} {F : Type v} (reg : V) (src : V × Nat) (d : Nat)
    (body : CFG.Body (V × Nat) K F) :
    Versioning.unpackBody [reg] src d body =
      .let2 (reg, d + 1) (reg, d + 2) (.val (.var src)) body :=
  Option.get_of_eq_some _ (by simp [Version.unpack, CFG.Body.ofRegion?, body_readback])

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

private theorem routes_saved (graph : CFG V K F) (exits : List K)
    (capture : Option (V × Ty Base))
    (R : Fin (Versioning.compile graph).blocks.length → Ty Base) (D : Fin exits.length → Ty Base)
    (slots : ∀ i : Fin graph.blocks.length,
      Versioning.slots graph graph.blocks[i].2 = capture.toList.map Prod.fst) :
    Routes (labelIndex (Versioning.compile graph).blocks exits) (Versioning.destinations graph)
      capture (SSA.FiniteSum.append R D)
      (SSA.FiniteSum.append (fun i => .product (R i) (savedType capture)) D) := by
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
        exact congrArg some (slots j)
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
    ∃ flat, body index names src = some flat ∧ checkBody types ctx flat = true := by
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

private theorem block_checked_empty [DecidableEq Base] [HasTy F (Ty Base)]
    {n labels : Nat} (graph : CFG V K F) (src : CFG.Block V K F)
    (index : K → Option (Fin labels)) (old new : Fin labels → Ty Base)
    (routes : Routes index (Versioning.destinations graph) none old new)
    (ctx : BoundCtx (Ty Base) n) (A : Ty Base)
    (empty : Versioning.slots graph src = [])
    (checked : sourceCheck index old (blockNames src.param) (.snoc ctx A) src.body = true) :
    ∃ flat, body index (blockNames (Versioning.compileBlock graph src).param)
      (Versioning.compileBlock graph src).body = some flat ∧
      checkBody new (.snoc ctx (.product A .unit)) flat = true := by
  obtain ⟨_, read, typed⟩ := checked_source checked
  obtain ⟨inside, hInside, tInside⟩ := version_body index _ none old new routes
    (Versioning.registers graph) src.body 2 _ _ _ _ _
    (block_scope src.param ctx A) (by intro _ _ h; cases h) (by intro _ _ h; cases h) read typed
  refine ⟨.let₂ (.bv 0) inside, ?_, ?_⟩
  · simp [Versioning.compileBlock, empty, unpack_empty, Versioning.blockVersions, Version.unpackCur,
      body, operand, value, blockNames, bindName]
    exact hInside
  · simpa [checkBody, infer, BoundCtx.get] using tInside

omit [DecidableEq K] in
private theorem read_pair [DecidableEq Base] [HasTy F (Ty Base)]
    {n labels : Nat} {index : K → Option (Fin labels)} {types : Fin labels → Ty Base}
    {names : Names (V × Nat) n} {ctx : BoundCtx (Ty Base) n} {packet x y : V × Nat}
    {i : Fin n} {A B : Ty Base} {tail : CFG.Body (V × Nat) K F} {inner : Flat F labels (n + 2)}
    (src : names packet = some i) (type : ctx.get i = .product A B)
    (read : body index (bindName (bindName names x) y) tail = some inner)
    (checked : checkBody types (.snoc (.snoc ctx A) B) inner = true) :
    body index names (.let2 x y (.val (.var packet)) tail) = some (.let₂ (.bv i) inner) ∧
      checkBody types ctx (.let₂ (.bv i) inner) = true :=
  ⟨by simp [body, operand, value, src, read], by simp [checkBody, infer, type, checked]⟩

private theorem block_checked_one [DecidableEq Base] [HasTy F (Ty Base)]
    {n labels : Nat} (graph : CFG V K F) (src : CFG.Block V K F)
    (index : K → Option (Fin labels)) (old new : Fin labels → Ty Base)
    (reg : V) (T : Ty Base)
    (routes : Routes index (Versioning.destinations graph) (some (reg, T)) old new)
    (ctx : BoundCtx (Ty Base) n) (A : Ty Base)
    (slots : Versioning.slots graph src = [reg])
    (keeps : KeepsCapture (some (reg, T)) src.body.toRegion)
    (checked : sourceCheck index old (blockNames src.param) (.snoc ctx A) src.body = true) :
    ∃ flat, body index (blockNames (Versioning.compileBlock graph src).param)
      (Versioning.compileBlock graph src).body = some flat ∧
      checkBody new (.snoc ctx (.product A (.product T .unit))) flat = true := by
  let p := src.param
  have distinct : reg ≠ p :=
    of_decide_eq_true ((List.mem_filter.mp (show reg ∈ Versioning.slots graph src from by simp [slots])).2)
  let initial := blockNames (n := n) (p, 0)
  let afterArg := bindName (bindName initial (p, 1)) (p, 2)
  let afterCapture := bindName (bindName afterArg (reg, 3)) (reg, 4)
  let ctx0 := ctx.snoc (.product A (.product T .unit))
  let ctx1 := (ctx0.snoc A).snoc (.product T .unit)
  let ctx2 := (ctx1.snoc T).snoc .unit
  let cur := Version.setv (Version.setv (fun _ => 0) p 1) reg 3
  have scope : Scope cur (blockNames p) (.snoc ctx A) afterCapture ctx2 := by
    intro r i hit
    by_cases eq : r = p
    · subst r
      have h : i = 0 := by simpa [blockNames, bindName] using hit.symm
      subst i
      exact ⟨(0 : Fin (n + 2)).succ.succ.succ,
        by simp [afterCapture, afterArg, cur, Version.setv, bindName, Ne.symm distinct], rfl⟩
    · simp [blockNames, bindName, eq] at hit
  have saved : SavedScope cur (some (reg, T)) afterCapture ctx2 := by
    intro r ty field
    cases field
    exact ⟨(0 : Fin (n + 4)).succ,
      by simp [afterCapture, cur, Version.setv, bindName], rfl⟩
  obtain ⟨_, source, typed⟩ := checked_source checked
  let inner := Versioning.versionBody src.body (Versioning.destinations graph) (Versioning.registers graph) cur 4
  obtain ⟨bodyOut, hBody, tBody⟩ := version_body index _ (some (reg, T)) old new routes
    (Versioning.registers graph) src.body 4 cur _ _ afterCapture ctx2 scope saved keeps source typed
  have record : afterArg (p, 2) = some 0 := by simp [afterArg, bindName]
  obtain ⟨hRecord, tRecord⟩ := read_pair (packet := (p, 2)) (names := afterArg) (i := 0)
    (ctx := ctx1) (x := (reg, 3)) (y := (reg, 4)) (tail := inner) record
    (show ctx1.get 0 = .product T .unit from rfl) hBody tBody
  have packet : initial (p, 0) = some 0 := by simp [initial, blockNames, bindName]
  obtain ⟨hPacket, tPacket⟩ := read_pair (packet := (p, 0)) (names := initial) (i := 0)
    (ctx := ctx0) (x := (p, 1)) (y := (p, 2)) packet
    (show ctx0.get 0 = .product A (.product T .unit) from rfl) hRecord tRecord
  refine ⟨_, ?_, tPacket⟩
  simp only [Versioning.compileBlock, slots, unpack_one, Versioning.blockVersions, Version.unpackCur]
  exact hPacket

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

private def capturedField (ctx : BoundCtx (Ty κ) n) (slot : Option (Fin n)) :
    Option (Register × Ty κ) :=
  slot.map fun i => (⟨i.val⟩, ctx.get i)

omit [DecidableEq κ] in
private theorem packetProfile_saved (R : Fin blocks → Ty κ) (saved : a.SavesCaptures)
    (slot : Option (Fin n)) (i : Fin (versioned).blocks.length)
    (slots : a.savedRegisters i = slot.toList.map (fun j => (⟨j.val⟩ : Register))) :
    a.packetProfile R saved i =
      .product (R (Fin.cast a.reversionCount i)) (savedType (capturedField context slot)) := by
  let typed := fun reg : Register => (reg, if bound : reg.down < n then
    context.get ⟨reg.down, bound⟩ else Ty.unit)
  have fieldsEq : (a.savedRegisters i).attach.map (fun reg =>
      (reg.val, context.get ⟨reg.val.down, saved i reg.val reg.property⟩)) =
      (a.savedRegisters i).map typed := by
    rw [← List.attach_map_val (l := a.savedRegisters i) (f := typed)]
    apply List.map_congr_left
    intro reg _
    simp [typed, saved i reg.val reg.property]
  unfold Lowered.packetProfile
  rw [fieldsEq, slots]
  cases slot with
  | none => rfl
  | some j => simp [capturedField, typed, savedType, LiveOut.recordType, j.isLt]

omit [DecidableEq κ] in
private theorem entry_saved (slot : Option (Fin n)) :
    SavedScope (fun _ => 0) (capturedField context slot)
      (first fun i : Fin n => ((⟨i.val⟩ : Register), (0 : Nat))) context := by
  intro reg A field
  cases slot with
  | none => cases field
  | some j =>
    cases field
    refine ⟨j, ?_, rfl⟩
    unfold first
    cases hit : (List.finRange n).find? (fun k => decide
        (((⟨k.val⟩ : Register), (0 : Nat)) = (⟨j.val⟩, 0))) with
    | none =>
      have := List.find?_eq_none.mp hit j (by simp)
      simp at this
    | some i =>
      have eq : ((⟨i.val⟩ : Register), (0 : Nat)) = (⟨j.val⟩, 0) :=
        of_decide_eq_true (List.find?_some
          (p := fun k : Fin n => decide (((⟨k.val⟩ : Register), (0 : Nat)) = (⟨j.val⟩, 0))) hit)
      exact congrArg some (Fin.ext (congrArg (ULift.down ∘ Prod.fst) eq))

omit [DecidableEq κ] [DecidableEq Label] in
private theorem kept_body (src : CFG.Body Register Label P.Instr) (slot : Option (Fin n))
    (kept : ∀ i, slot = some i → (⟨i.val⟩ : Register) ∉ src.toRegion.bound) :
    KeepsCapture (capturedField context slot) src.toRegion := by
  intro reg A field
  cases slot with
  | none => cases field
  | some i =>
    cases field
    exact kept i rfl

set_option maxHeartbeats 400000 in
private theorem compiled_success_at (R : Fin blocks → Ty κ) (saved : a.SavesCaptures)
    (slot : Option (Fin n))
    (layout : ∀ i, a.savedRegisters i = slot.toList.map (fun j => (⟨j.val⟩ : Register)))
    (kept : ∀ j, slot = some j → keepsEntryCapture a j = true)
    (checked : checks a R = true) :
    ∃ table, compile attached exits (fun i : Fin n => (⟨i.val⟩ : Register)) = some table ∧
      let new := SSA.FiniteSum.append (a.packetProfile R saved) exitTypes
      checkBody new context table.entry = true ∧
        ∀ i, checkBody new (.snoc context (a.packetProfile R saved i)) (table.block i) = true := by
  let index := labelIndex (versioned).blocks exits
  let captures : Fin n → Register := fun i => ⟨i.val⟩
  let original := fun i => R (Fin.cast a.reversionCount i)
  let capture := capturedField context slot
  let expanded := fun i => Ty.product (original i) (savedType capture)
  have profile : a.packetProfile R saved = expanded :=
    funext (fun i => packetProfile_saved a R saved slot i (layout i))
  rw [profile]
  let old := SSA.FiniteSum.append original exitTypes
  let new := SSA.FiniteSum.append expanded exitTypes
  have order : slot.toList.map (fun j => (⟨j.val⟩ : Register)) = capture.toList.map Prod.fst := by
    cases slot <;> rfl
  have slots (i : Fin (attached).blocks.length) :
      Versioning.slots attached (attached).blocks[i].2 = capture.toList.map Prod.fst :=
    (layout (Fin.cast (List.length_map _).symm i)).trans order
  have route := routes_saved attached exits capture original exitTypes slots
  have entryKeeps := kept_body (context := context) (attached).entry slot fun j hit =>
    of_decide_eq_true (Bool.and_eq_true_iff.mp (kept j hit)).1
  obtain ⟨sourceEntry, sourceBlocks⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨_, read, typed⟩ := checked_source sourceEntry
  obtain ⟨entry, hEntry, tEntry⟩ := version_body index _ capture old new route (Versioning.registers attached)
    (attached).entry 0 (fun _ => 0) _ _ _ _ (entry_scope captures context)
    (entry_saved (context := context) slot) entryKeeps read typed
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
    have bodyKeeps := kept_body (context := context) (attached).blocks[j].2.body slot fun k hit =>
      of_decide_eq_true (List.all_eq_true.mp (Bool.and_eq_true_iff.mp (kept k hit)).2 _
        (List.getElem_mem (l := (attached).blocks) j.isLt))
    cases slot with
    | none =>
      exact block_checked_empty attached (attached).blocks[j].2 index old new route
        context (original i) (slots j) checkAt
    | some k =>
      exact block_checked_one attached (attached).blocks[j].2 index old new ⟨k.val⟩
        (context.get k) route context (original i) (slots j) bodyKeeps checkAt
  obtain ⟨rows, hRows, tRows⟩ := tabulate_checked byBlock
  exact ⟨⟨entry, rows⟩, by
    unfold compile elaborate
    change (body index (first fun i => (captures i, 0)) (versioned).entry).bind
      (fun outgoing => (tabulate (versioned).blocks.length
        (fun i => body index (blockNames (versioned).blocks[i].2.param)
          (versioned).blocks[i].2.body)).map (FiniteCFG.mk outgoing)) = some (FiniteCFG.mk entry rows)
    rw [show body index (first fun i => (captures i, 0)) (versioned).entry = some entry from hEntry]
    exact congrArg (Option.map (FiniteCFG.mk entry)) hRows, tEntry, tRows⟩

theorem compiled_success (R : Fin blocks → Ty κ) (saved : a.SavesCaptures)
    (empty : ∀ i, a.savedRegisters i = []) (checked : checks a R = true) :
    ∃ table, compile attached exits (fun i : Fin n => (⟨i.val⟩ : Register)) = some table ∧
      let new := SSA.FiniteSum.append (a.packetProfile R saved) exitTypes
      checkBody new context table.entry = true ∧
        ∀ i, checkBody new (.snoc context (a.packetProfile R saved i)) (table.block i) = true :=
  compiled_success_at a R saved none empty (fun _ h => nomatch h) checked

theorem compiled_success_capture (R : Fin blocks → Ty κ) (saved : a.SavesCaptures)
    (slot : Fin n) (layout : ∀ i, a.savedRegisters i = [⟨slot.val⟩])
    (kept : keepsEntryCapture a slot = true) (checked : checks a R = true) :
    ∃ table, compile attached exits (fun i : Fin n => (⟨i.val⟩ : Register)) = some table ∧
      let new := SSA.FiniteSum.append (a.packetProfile R saved) exitTypes
      checkBody new context table.entry = true ∧
        ∀ i, checkBody new (.snoc context (a.packetProfile R saved i)) (table.block i) = true :=
  compiled_success_at a R saved (some slot) layout
    (fun _ h => Option.some.inj h ▸ kept) checked

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
