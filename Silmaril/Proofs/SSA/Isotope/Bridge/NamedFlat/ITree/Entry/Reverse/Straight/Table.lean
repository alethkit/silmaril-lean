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

private theorem unpack_cons {V K : Type u} {F : Type v} (reg : V) (rest : List V)
    (src : V × Nat) (d : Nat) (body : CFG.Body (V × Nat) K F) :
    Versioning.unpackBody (reg :: rest) src d body =
      .let2 (reg, d + 1) (reg, d + 2) (.val (.var src))
        (Versioning.unpackBody rest (reg, d + 2) (d + 2) body) := by
  have read : CFG.Body.ofRegion? (Version.unpack rest (reg, d + 2) (d + 2) body.toRegion) =
      some (Versioning.unpackBody rest (reg, d + 2) (d + 2) body) := (Option.some_get _).symm
  exact Option.get_of_eq_some _ (by simp [Version.unpack, CFG.Body.ofRegion?, read])

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
    (capture : List (V × Ty Base))
    (R : Fin (Versioning.compile graph).blocks.length → Ty Base) (D : Fin exits.length → Ty Base)
    (slots : ∀ i : Fin graph.blocks.length,
      Versioning.slots graph graph.blocks[i].2 = capture.map Prod.fst) :
    Routes (labelIndex (Versioning.compile graph).blocks exits) (Versioning.destinations graph)
      capture (SSA.FiniteSum.append R D)
      (SSA.FiniteSum.append (fun i => .product (R i) (LiveOut.recordType capture)) D) := by
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

omit [DecidableEq K] in
/-- Type the actual tuple decoder. At each prefix, track the already
decoded fields at their current versions and the remaining tuple at its
named temporary. The continuation can use every decoded field. -/
private theorem unpack_checked [DecidableEq Base] [HasTy F (Ty Base)]
    {n labels : Nat} (index : K → Option (Fin labels)) (types : Fin labels → Ty Base)
    (remaining known : List (V × Ty Base))
    (distinct : ((remaining.reverse ++ known).map Prod.fst).Nodup)
    (cur : V → Nat) (d : Nat)
    (names : Names (V × Nat) n) (ctx : BoundCtx (Ty Base) n) (packet : V × Nat)
    (i : Fin n) (hit : names packet = some i) (type : ctx.get i = LiveOut.recordType remaining)
    (scope : SavedScope cur known names ctx) (tail : CFG.Body (V × Nat) K F)
    (inside : ∀ {m} (target : Names (V × Nat) m) (typed : BoundCtx (Ty Base) m),
      SavedScope (Version.unpackCur (remaining.map Prod.fst) cur d)
        (remaining.reverse ++ known) target typed →
      ∃ flat, body index target tail = some flat ∧ checkBody types typed flat = true) :
    ∃ flat, body index names (Versioning.unpackBody (remaining.map Prod.fst) packet d tail) = some flat ∧
      checkBody types ctx flat = true := by
  induction remaining generalizing known n cur d packet with
  | nil => simpa [unpack_empty, Version.unpackCur] using inside names ctx scope
  | cons field rest ih =>
    obtain ⟨reg, A⟩ := field
    let next := Version.setv cur reg (d + 1)
    let target := bindName (bindName names (reg, d + 1)) (reg, d + 2)
    let typed := (ctx.snoc A).snoc (LiveOut.recordType rest)
    have distinctNext : ((rest.reverse ++ (reg, A) :: known).map Prod.fst).Nodup := by
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using distinct
    have knownDistinct : (reg :: known.map Prod.fst).Nodup :=
      (List.nodup_append.mp (by simpa only [List.map_append, List.map_cons] using distinctNext)).2.1
    have fresh := (List.nodup_cons.mp knownDistinct).1
    have nextScope : SavedScope next ((reg, A) :: known) target typed := by
      intro r T mem
      rcases List.mem_cons.mp mem with eq | old
      · cases eq
        exact ⟨(0 : Fin (n + 1)).succ, by simp [next, target, Version.setv, bindName], rfl⟩
      · have ne : r ≠ reg := fun eq => fresh (List.mem_map.mpr ⟨(r, T), old, eq⟩)
        obtain ⟨j, read, ty⟩ := scope r T old
        exact ⟨j.succ.succ, by simp [next, target, Version.setv, bindName, ne, read], ty⟩
    obtain ⟨flat, read, checked⟩ := ih ((reg, A) :: known) distinctNext next (d + 2)
      target typed (reg, d + 2) 0 (by simp [target, bindName]) rfl nextScope
      (fun {_} out outCtx inScope => inside out outCtx (by
        simpa only [List.map_cons, Version.unpackCur, List.reverse_cons, List.append_assoc,
          List.singleton_append] using inScope))
    have result := read_pair (packet := packet) (i := i) (x := (reg, d + 1)) (y := (reg, d + 2))
      (show names packet = some i from hit) (show ctx.get i = .product A (LiveOut.recordType rest) from type)
      read checked
    exact ⟨_, by simpa only [List.map_cons, unpack_cons] using result.1, result.2⟩

private theorem block_checked [DecidableEq Base] [HasTy F (Ty Base)]
    {n labels : Nat} (graph : CFG V K F) (src : CFG.Block V K F)
    (index : K → Option (Fin labels)) (old new : Fin labels → Ty Base)
    (captures : List (V × Ty Base))
    (routes : Routes index (Versioning.destinations graph) captures old new)
    (ctx : BoundCtx (Ty Base) n) (A : Ty Base)
    (slots : Versioning.slots graph src = captures.map Prod.fst)
    (keeps : KeepsCapture captures src.body.toRegion)
    (checked : sourceCheck index old (blockNames src.param) (.snoc ctx A) src.body = true) :
    ∃ flat, body index (blockNames (Versioning.compileBlock graph src).param)
      (Versioning.compileBlock graph src).body = some flat ∧
      checkBody new (.snoc ctx (.product A (LiveOut.recordType captures))) flat = true := by
  let p := src.param
  let initial := blockNames (n := n) (p, 0)
  let afterArg := bindName (bindName initial (p, 1)) (p, 2)
  let ctx0 := ctx.snoc (.product A (LiveOut.recordType captures))
  let ctx1 := (ctx0.snoc A).snoc (LiveOut.recordType captures)
  let cur := Version.setv (fun _ => 0) p 1
  let versions := Version.unpackCur (captures.map Prod.fst) cur 2
  let inner := Versioning.versionBody src.body (Versioning.destinations graph) (Versioning.registers graph)
    versions (2 + 2 * captures.length)
  have distinct : ((captures.reverse ++ [(p, A)]).map Prod.fst).Nodup := by
    rw [List.map_append, List.map_reverse, ← slots, List.nodup_append]
    refine ⟨List.nodup_reverse.mpr (List.Nodup.filter _ (List.nodup_dedup _)), by simp, ?_⟩
    intro reg mem other selected
    have ne := of_decide_eq_true ((List.mem_filter.mp (List.mem_reverse.mp mem)).2)
    have eq : other = p := by simpa using selected
    exact eq ▸ ne
  have arg : SavedScope cur [(p, A)] afterArg ctx1 := by
    intro reg T mem
    have eq : (reg, T) = (p, A) := by simpa using mem
    cases eq
    exact ⟨(0 : Fin (n + 2)).succ, by simp [cur, afterArg, Version.setv, bindName], rfl⟩
  obtain ⟨_, source, typed⟩ := checked_source checked
  obtain ⟨decoded, hDecoded, tDecoded⟩ := unpack_checked index new captures [(p, A)] distinct
    cur 2
    afterArg ctx1 (p, 2) 0 (by simp [afterArg, bindName]) rfl arg inner (by
      intro m names types all
      have scope : Scope versions (blockNames p) (.snoc ctx A) names types := by
        intro r i hit
        by_cases same : r = p
        · subst r
          have eq : i = 0 := by simpa [blockNames, bindName] using hit.symm
          subst i
          exact all p A (by simp)
        · simp [blockNames, bindName, same] at hit
      have saved : SavedScope versions captures names types :=
        fun r T mem => all r T (by simp [mem])
      exact version_body index _ captures old new routes (Versioning.registers graph) src.body
        (2 + 2 * captures.length) versions _ _ names types scope saved keeps source typed)
  have packet : initial (p, 0) = some 0 := by simp [initial, blockNames, bindName]
  obtain ⟨hPacket, tPacket⟩ := read_pair (packet := (p, 0)) (names := initial) (i := 0)
    (ctx := ctx0) (x := (p, 1)) (y := (p, 2)) packet
    (show ctx0.get 0 = .product A (LiveOut.recordType captures) from rfl) hDecoded tDecoded
  refine ⟨_, ?_, tPacket⟩
  simpa only [Versioning.compileBlock, slots, Versioning.blockVersions, List.length_map] using hPacket

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
private theorem packetProfile_saved (R : Fin blocks → Ty κ) (saved : a.SavesCaptures)
    (slots : List (Fin n)) (i : Fin (versioned).blocks.length)
    (layout : a.savedRegisters i = slots.map (fun j => (⟨j.val⟩ : Register))) :
    a.packetProfile R saved i =
      .product (R (Fin.cast a.reversionCount i)) (LiveOut.recordType (captureFields context slots)) := by
  let typed := fun reg : Register => (reg, if bound : reg.down < n then
    context.get ⟨reg.down, bound⟩ else Ty.unit)
  have fieldsEq : (a.savedRegisters i).attach.map (fun reg =>
      (reg.val, context.get ⟨reg.val.down, saved i reg.val reg.property⟩)) =
      (a.savedRegisters i).map typed := by
    rw [← List.attach_map_val (l := a.savedRegisters i) (f := typed)]
    apply List.map_congr_left
    intro reg _
    simp [typed, saved i reg.val reg.property]
  have types : (slots.map (fun j => (⟨j.val⟩ : Register))).map typed = captureFields context slots := by
    simp only [captureFields, List.map_map]
    apply List.map_congr_left
    intro j _
    simp [typed, j.isLt]
  simp only [Lowered.packetProfile, fieldsEq, layout, types]

omit [DecidableEq κ] in
private theorem entry_saved (slots : List (Fin n)) :
    SavedScope (fun _ => 0) (captureFields context slots)
      (first fun i : Fin n => ((⟨i.val⟩ : Register), (0 : Nat))) context := by
  intro reg A field
  obtain ⟨j, _, eq⟩ := List.mem_map.mp field
  cases eq
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
private theorem kept_body (src : CFG.Body Register Label P.Instr) (slots : List (Fin n))
    (kept : ∀ i ∈ slots, (⟨i.val⟩ : Register) ∉ src.toRegion.bound) :
    KeepsCapture (captureFields context slots) src.toRegion := by
  intro reg A field
  obtain ⟨i, member, eq⟩ := List.mem_map.mp field
  cases eq
  exact kept i member

set_option maxHeartbeats 400000 in
theorem compiled_success_captures (R : Fin blocks → Ty κ) (saved : a.SavesCaptures)
    (slots : List (Fin n))
    (layout : ∀ i, a.savedRegisters i = slots.map (fun j => (⟨j.val⟩ : Register)))
    (kept : keepsEntryCaptures a slots = true)
    (checked : checks a R = true) :
    ∃ table, compile attached exits (fun i : Fin n => (⟨i.val⟩ : Register)) = some table ∧
      let new := SSA.FiniteSum.append (a.packetProfile R saved) exitTypes
      checkBody new context table.entry = true ∧
        ∀ i, checkBody new (.snoc context (a.packetProfile R saved i)) (table.block i) = true := by
  let index := labelIndex (versioned).blocks exits
  let captures : Fin n → Register := fun i => ⟨i.val⟩
  let original := fun i => R (Fin.cast a.reversionCount i)
  let capture := captureFields context slots
  let expanded := fun i => Ty.product (original i) (LiveOut.recordType capture)
  have profile : a.packetProfile R saved = expanded :=
    funext (fun i => packetProfile_saved a R saved slots i (layout i))
  rw [profile]
  let old := SSA.FiniteSum.append original exitTypes
  let new := SSA.FiniteSum.append expanded exitTypes
  have order : slots.map (fun j => (⟨j.val⟩ : Register)) = capture.map Prod.fst := by
    simp [capture, captureFields, Function.comp_def]
  have savedAt (i : Fin (attached).blocks.length) :
      Versioning.slots attached (attached).blocks[i].2 = capture.map Prod.fst :=
    (layout (Fin.cast (List.length_map _).symm i)).trans order
  have route := routes_saved attached exits capture original exitTypes savedAt
  have keptAt := List.all_eq_true.mp kept
  have entryKeeps := kept_body (context := context) (attached).entry slots fun j hit =>
    of_decide_eq_true (Bool.and_eq_true_iff.mp (keptAt j hit)).1
  obtain ⟨sourceEntry, sourceBlocks⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨_, read, typed⟩ := checked_source sourceEntry
  obtain ⟨entry, hEntry, tEntry⟩ := version_body index _ capture old new route (Versioning.registers attached)
    (attached).entry 0 (fun _ => 0) _ _ _ _ (entry_scope captures context)
    (entry_saved (context := context) slots) entryKeeps read typed
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
    have bodyKeeps := kept_body (context := context) (attached).blocks[j].2.body slots fun k hit =>
      of_decide_eq_true (List.all_eq_true.mp (Bool.and_eq_true_iff.mp (keptAt k hit)).2 _
        (List.getElem_mem (l := (attached).blocks) j.isLt))
    exact block_checked attached (attached).blocks[j].2 index old new capture route
      context (original i) (savedAt j) bodyKeeps checkAt
  obtain ⟨rows, hRows, tRows⟩ := tabulate_checked byBlock
  exact ⟨⟨entry, rows⟩, by
    unfold compile elaborate
    change (body index (first fun i => (captures i, 0)) (versioned).entry).bind
      (fun outgoing => (tabulate (versioned).blocks.length
        (fun i => body index (blockNames (versioned).blocks[i].2.param)
          (versioned).blocks[i].2.body)).map (FiniteCFG.mk outgoing)) = some (FiniteCFG.mk entry rows)
    rw [show body index (first fun i => (captures i, 0)) (versioned).entry = some entry from hEntry]
    exact congrArg (Option.map (FiniteCFG.mk entry)) hRows, tEntry, tRows⟩

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
