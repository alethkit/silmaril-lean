module

public import Silmaril.X86.Concurrency.Sqlite.Release.Defs
import Silmaril.X86.MemoryModel.Tso.Thms

public section

namespace Silmaril.Proofs.X86.Concurrency.Sqlite.Release

open Silmaril.X86.Concurrency.Sqlite Silmaril.X86.Concurrency.Sqlite.Release
open Silmaril.Machine.SqliteControl
open Silmaril.X86.MemoryModel.Tso hiding Execution
open Silmaril.X86.MemoryModel

private theorem flushes_preserve {s t : XState Nat} {lock : Nat} (steps : XFlushes s t)
    (avoids : BuffersAvoid s lock) :
    t.memory lock = s.memory lock ∧ BuffersAvoid t lock := by
  induction steps with
  | refl => exact ⟨rfl, avoids⟩
  | tail _ last ih =>
    obtain ⟨framed, safe⟩ := ih
    cases last with
    | head tid address bytes rest oldest =>
      have outside := safe tid (address, bytes) (oldest ▸ List.mem_cons_self)
      refine ⟨by simpa [writeMem, outside], ?_⟩
      intro other entry member
      by_cases same : other = tid
      · subst other
        apply safe tid entry
        rw [oldest]
        exact List.mem_cons_of_mem _ (by simpa using member)
      · exact safe other entry (by simpa [Function.update_of_ne same] using member)

private theorem weak_release {s t : XState Nat} {tid lock : Nat}
    (avoids : BuffersAvoid s lock) (releases : XWeakStep s (releaseEvent tid lock) t) :
    t.memory lock = some 0 ∧ t.buffer tid = [] := by
  obtain ⟨mid, before, _, _, _, after⟩ := weak_rmw_atomic releases
  have safe := (flushes_preserve before avoids).2
  have final := (flushes_preserve after safe).1
  exact ⟨by simpa [writeMem, entryByte] using final, weak_rmw_empty releases⟩

private theorem vm_release (tid : Nat) (busy rc : Int32) :
    ([Event.released tid], ⟨none, busy⟩) ∈ Layer.behaviors .control (releaseInput tid busy rc) := by
  let initial := releaseInput tid busy rc
  let final := initial.advance tid (.returnResult rc) ⟨none, busy⟩
  have stepReleases : Step initial (some (.released tid)) final := by
    exact ⟨tid, .tick, _, rfl, by simp [step, initial, final, releaseInput]⟩
  exact ⟨final, .more stepReleases (.done final), rfl⟩

private theorem release_bytes (tid lock : Nat) :
    accessBytes (releaseEvent tid lock) ⊆ {lock} := by
  intro a ha
  change lock ≤ a ∧ a < lock + 1 at ha
  exact show a = lock by omega

theorem confined_sound (tid lock : Nat) (busy rc : Int32) :
    Sound .fifo id (IsRelease tid lock) (releaseProjection tid lock busy)
      (releaseFootprint lock) (confined tid lock busy rc) := by
  rintro ⟨initial, spec⟩ hpair ⟨events, last⟩ path selected
  obtain ⟨avoids, _, eq⟩ : BuffersAvoid initial lock ∧ initial.memory lock = some 1 ∧
      spec = releaseInput tid busy rc := hpair
  subst spec
  change Tso.Execution XWeakStep initial events last at path
  have eq : events = [releaseEvent tid lock] := selected
  subst events
  have edge : XWeakStep initial (releaseEvent tid lock) last := by
    cases path with
    | cons step tail => cases tail; exact step
  have unlocked := (weak_release avoids edge).1
  refine ⟨?_, ?_⟩
  · have observation : (releaseProjection tid lock busy).observe (model := .fifo) ⟨[releaseEvent tid lock], last⟩ =
        (([Event.released tid], ⟨none, busy⟩) : Layer.control.Observation) := by
      apply Prod.ext
      · change List.filterMap
          (fun event : XEvent Nat => if event = releaseEvent tid lock then some (Event.released tid) else none)
          [releaseEvent tid lock] = [Event.released tid]
        simp [List.filterMap_nil]
      · change releasedView tid lock busy last.memory = _
        simp [releasedView, unlocked]
    change (releaseProjection tid lock busy).observe (model := .fifo) ⟨[releaseEvent tid lock], last⟩ ∈
      Layer.behaviors .control (releaseInput tid busy rc)
    rw [observation]
    exact vm_release tid busy rc
  · rintro addr ⟨event, member, accessed⟩
    have same : event = releaseEvent tid lock := List.mem_singleton.mp member
    subst event
    exact release_bytes tid lock accessed

private theorem run_nil {initial after : Config Phase} {events : List Event}
    (path : Run Step initial events after) (eq : events = []) : after = initial := by
  cases path with
  | done => rfl
  | more step _ =>
    obtain ⟨_, _, label, rfl, _⟩ := step
    simp at eq

private theorem release_owner {initial after : Config Phase} {events : List Event} {tid : Nat}
    (path : Run Step initial events after) (eq : events = [.released tid]) :
    after.shared.owner = none := by
  cases path with
  | done => simp at eq
  | more edge tail =>
    obtain ⟨actor, input, label, rfl, stepEdge⟩ := edge
    simp only [Option.toList_some, List.singleton_append, List.cons.injEq] at eq
    obtain ⟨rfl, nil⟩ := eq
    cases run_nil tail nil
    cases pc : initial.threads actor <;> cases input <;> simp [step, pc] at stepEdge
    exact congrArg (fun cfg : Config Phase => cfg.shared.owner) stepEdge.2.2.symm

private def interference : XState Nat :=
  enqueue (xembed fun _ => some 1) 1 0 [1]

private def afterRmw : XState Nat := {interference with memory := writeMem interference.memory 0 [0]}

private def afterInterference : XState Nat :=
  ⟨writeMem afterRmw.memory 0 [1], Function.update afterRmw.buffer 1 []⟩

private theorem interfering_run :
    MemorySemantics.fifo.Executes interference ⟨[releaseEvent 0 0], afterInterference⟩ := by
  have rmw : XStep interference (releaseEvent 0 0) afterRmw :=
    .rmw interference 0 0 [1] [0] (by decide) (by decide) rfl
  have flush : XFlush afterRmw afterInterference := .head _ 1 0 [1] [] (by decide)
  exact .cons ⟨_, _, .refl, rmw, .single flush⟩ (.nil _)

theorem top_unsound (allowed : XState Nat → Config Phase → Set Nat) :
    ¬ Sound .fifo id (IsRelease 0 0) (releaseProjection 0 0 0)
      allowed ⊤ := by
  intro sound
  have observation := (sound (interference, releaseInput 0 0 0) trivial _
    interfering_run rfl).1
  have obs : ([Event.released 0], ({ owner := some 0, busyCount := 0 } : Shared)) ∈
      Layer.behaviors .control (releaseInput 0 0 0) := observation
  obtain ⟨after, path, shared⟩ := obs
  have unlocked := release_owner path rfl
  rw [shared] at unlocked
  contradiction

private theorem flushes_preserve_view {s t : XState Nat} {owner addr : Nat} (steps : XFlushes s t)
    (confined : PeerBuffersAvoid s owner addr) :
    viewMem t owner addr = viewMem s owner addr ∧ PeerBuffersAvoid t owner addr := by
  induction steps with
  | refl => exact ⟨rfl, confined⟩
  | tail _ last ih =>
    obtain ⟨frame, safe⟩ := ih
    cases last with
    | head actor base bytes rest oldest =>
      refine ⟨?_, ?_⟩
      · rw [← frame]
        by_cases same : actor = owner
        · subst actor
          simp [viewMem, writeMem, oldest, readBufByte, Option.or_assoc]
        · have outside := safe actor same (base, bytes) (oldest ▸ List.mem_cons_self)
          simp [viewMem, writeMem, Function.update_of_ne (Ne.symm same), outside]
      · intro peer notOwner entry member
        by_cases same : peer = actor
        · subst peer
          apply safe actor notOwner entry
          rw [oldest]
          exact List.mem_cons_of_mem _ (by simpa using member)
        · exact safe peer notOwner entry (by simpa [Function.update_of_ne same] using member)

private theorem readBufByte_append (address : Nat) (front rest : List (Nat × List Byte)) :
    readBufByte address (front ++ rest) =
      (readBufByte address rest).or (readBufByte address front) := by
  induction front with
  | nil => simp [readBufByte]
  | cons head front ih =>
    obtain ⟨base, bytes⟩ := head
    simp [readBufByte, ih, Option.or_assoc]

private theorem view_enqueue_owner (state : XState Nat) (owner base address : Nat) (bytes : List Byte) :
    viewMem (enqueue state owner base bytes) owner address =
      (entryByte base bytes address).or (viewMem state owner address) := by
  simp [viewMem, enqueue, readBufByte_append, readBufByte, Option.or_assoc]

private theorem owner_step_view {initial final : XState Nat} {event : XEvent Nat} {owner address : Nat}
    (step : XWeakStep initial event final) (actor : event.thread = owner)
    (confined : PeerBuffersAvoid initial owner address) :
    viewMem final owner address = byteEffect event address (viewMem initial owner address) ∧
      PeerBuffersAvoid final owner address := by
  obtain ⟨_, _, before, issued, after⟩ := step
  obtain ⟨prior, safe⟩ := flushes_preserve_view before confined
  have afterIssue : ∀ {s t : XState Nat} {event : XEvent Nat}, XStep s event t →
      event.thread = owner → PeerBuffersAvoid s owner address →
      viewMem t owner address = byteEffect event address (viewMem s owner address) ∧
        PeerBuffersAvoid t owner address := by
    intro s t event edge h safe
    cases edge with
    | load => exact ⟨rfl, safe⟩
    | fence => exact ⟨rfl, safe⟩
    | store tid base bytes =>
      have same : tid = owner := h
      subst tid
      refine ⟨view_enqueue_owner s owner base address bytes, ?_⟩
      intro peer notOwner entry membership
      exact safe peer notOwner entry (by simpa [enqueue, Function.update_of_ne notOwner] using membership)
    | rmw tid base old bytes empty _ _ =>
      have same : tid = owner := h
      subst tid
      exact ⟨by simp [byteEffect, viewMem, writeMem, empty, readBufByte], safe⟩
  obtain ⟨updated, safeIssue⟩ := afterIssue issued actor safe
  obtain ⟨view, safeFinal⟩ := flushes_preserve_view after safeIssue
  exact ⟨view.trans (updated.trans (congrArg (byteEffect event address) prior)), safeFinal⟩

theorem owner_trace_view {initial final : XState Nat} {events : List (XEvent Nat)} {owner address : Nat}
    (trace : Tso.Execution XWeakStep initial events final)
    (actors : ∀ event ∈ events, event.thread = owner)
    (confined : PeerBuffersAvoid initial owner address) :
    viewMem final owner address =
      events.foldl (fun before event => byteEffect event address before) (viewMem initial owner address) ∧
      PeerBuffersAvoid final owner address := by
  induction trace with
  | nil _ => exact ⟨rfl, confined⟩
  | cons step tail ih =>
    obtain ⟨affected, safe⟩ := owner_step_view step (actors _ List.mem_cons_self) confined
    obtain ⟨last, lastSafe⟩ :=
      ih (fun event member => actors event (List.mem_cons_of_mem _ member)) safe
    exact ⟨by rw [last, List.foldl_cons, affected], lastSafe⟩

theorem release_publishes {s t : XState Nat} {tid lock payload : Nat}
    (separate : payload ≠ lock) (confined : PeerBuffersAvoid s tid payload)
    (releases : XWeakStep s (releaseEvent tid lock) t) :
    t.memory payload = viewMem s tid payload := by
  obtain ⟨mid, before, _, _, _, after⟩ := weak_rmw_atomic releases
  have ⟨beforeView, safeMid⟩ := flushes_preserve_view before confined
  let updated := {mid with memory := writeMem mid.memory lock [0]}
  have outside : entryByte lock [0#8] payload = none := by
    unfold entryByte
    split
    · simp [show payload - lock ≠ 0 by omega]
    · rfl
  have drained := weak_rmw_empty releases
  have afterView := (flushes_preserve_view after (show PeerBuffersAvoid updated tid payload from safeMid)).1
  calc
    t.memory payload = viewMem t tid payload := by simp [viewMem, drained, readBufByte]
    _ = viewMem updated tid payload := afterView
    _ = viewMem mid tid payload := by simp [updated, viewMem, writeMem, outside]
    _ = viewMem s tid payload := beforeView

/-- A confined full dword release clears the four-byte lock and publishes the
owner's view outside it, at any byte no peer can overwrite from a buffer. -/
theorem dword_release {s t : XState Nat} {tid lock : Nat}
    (lockConfined : ∀ addr, lock ≤ addr → addr < lock + 4 → BuffersAvoid s addr)
    (release : XWeakStep s (.rmw tid lock [1, 0, 0, 0] [0, 0, 0, 0]) t) :
    (∀ addr, lock ≤ addr → addr < lock + 4 → t.memory addr = some 0) ∧
    t.buffer tid = [] ∧
    ∀ addr, (addr < lock ∨ lock + 4 ≤ addr) → PeerBuffersAvoid s tid addr →
      t.memory addr = viewMem s tid addr := by
  obtain ⟨mid, before, ownerEmpty, _, _, after⟩ := weak_rmw_atomic release
  let written := {mid with memory := writeMem mid.memory lock [0, 0, 0, 0]}
  have drained := weak_rmw_empty release
  have observed {addr : Nat} (safe : PeerBuffersAvoid s tid addr) :
      t.memory addr = written.memory addr := by
    have retained := (flushes_preserve_view before safe).2
    have atWrite : PeerBuffersAvoid written tid addr := retained
    have eq := (flushes_preserve_view after atWrite).1
    simpa [viewMem, drained, written, ownerEmpty, readBufByte] using eq
  refine ⟨?_, drained, ?_⟩
  · intro addr low high
    rw [observed (fun who _ => lockConfined addr low high who)]
    have offset : addr - lock = 0 ∨ addr - lock = 1 ∨ addr - lock = 2 ∨ addr - lock = 3 := by omega
    rcases offset with equal | equal | equal | equal <;> simp [written, writeMem, entryByte, low, equal]
  · intro addr outside safe
    have zero : entryByte lock [0#8, 0#8, 0#8, 0#8] addr = none := by
      unfold entryByte
      split
      · apply List.getElem?_eq_none
        simp
        omega
      · rfl
    calc
      t.memory addr = written.memory addr := observed safe
      _ = mid.memory addr := by simp [written, writeMem, zero]
      _ = viewMem s tid addr := by
        have eq := (flushes_preserve_view before safe).1
        simpa [viewMem, ownerEmpty, readBufByte] using eq

theorem sc_release_matches {initial last : Silmaril.X86.MemoryModel.Tso.Mem} {tid lock : Nat} {busy rc : Int32}
    (startsLocked : initial lock = some 1)
    (path : Tso.Execution SCStep initial [releaseEvent tid lock] last) :
    (releaseProjection tid lock busy).observe (model := .fifo)
      ⟨[releaseEvent tid lock], xembed last⟩ ∈
      Layer.behaviors .control (releaseInput tid busy rc) := by
  have h : BuffersAvoid (xembed (Tid := Nat) initial) lock := by
    intro _ _ member
    cases member
  have sound := confined_sound tid lock busy rc
  exact (sound (xembed initial, releaseInput tid busy rc) ⟨h, startsLocked, rfl⟩
    ⟨[releaseEvent tid lock], xembed last⟩ (of_sc_x path) rfl).1

/-- An owner has a payload write pending. The locked release is preceded by
one actual FIFO flush, publishes the payload, and is observable as release. -/

theorem sc_release_witness :
    let initial : Tso.Mem := fun a => some (if a = 0 then 1 else 0)
    let final := writeMem initial 0 [0]
    MemorySemantics.sc.Executes initial ⟨[releaseEvent 0 0], final⟩ ∧
      ([Event.released 0], (⟨none, 0⟩ : Shared)) ∈
        Layer.behaviors .control (releaseInput 0 0 0) := by
  dsimp only
  let initial : Tso.Mem := fun a => some (if a = 0 then 1 else 0)
  have step : SCStep initial (releaseEvent 0 0) (writeMem initial 0 [0]) :=
    .rmw initial 0 0 [1] [0] (by decide) rfl
  have path : Tso.Execution SCStep initial [releaseEvent 0 0] (writeMem initial 0 [0]) :=
    .cons step (.nil _)
  exact ⟨path, sc_release_matches (busy := 0) (rc := 0) (by decide) path⟩

theorem pending_owner_witness :
    let initial := enqueue (xembed (Tid := Nat) fun a => some (if a = 0 then 1 else 0)) 0 1 [42]
    (initial, releaseInput 0 0 0) ∈ confined 0 0 0 0 ∧
      ∃ run, MemorySemantics.fifo.Executes initial run ∧ IsRelease 0 0 initial run ∧
        initial.memory 1 = some 0 ∧ viewMem initial 0 1 = some 42 ∧
        run.final.memory 1 = some 42 ∧ run.final.buffer 0 = [] := by
  let base : Silmaril.X86.MemoryModel.Tso.Mem := fun a => some (if a = 0 then 1 else 0)
  let initial : XState Nat := enqueue (xembed base) 0 1 [42]
  let mid : XState Nat := ⟨writeMem initial.memory 1 [42], Function.update initial.buffer 0 []⟩
  let final : XState Nat := {mid with memory := writeMem mid.memory 0 [0]}
  have avoids : BuffersAvoid initial 0 := by
    intro actor entry member
    by_cases same : actor = 0
    · subst actor
      have eq : entry = (1, [42#8]) := by simpa [initial, enqueue, xembed] using member
      subst entry
      decide
    · simp [initial, enqueue, xembed, Function.update_of_ne same] at member
  have flush : XFlush initial mid := .head initial 0 1 [42] [] (by decide)
  have rmw : XStep mid (releaseEvent 0 0) final :=
    .rmw mid 0 0 [1] [0] (by decide) (by decide) rfl
  exact ⟨⟨avoids, rfl, rfl⟩, ⟨[releaseEvent 0 0], final⟩,
    .cons ⟨mid, final, .single flush, rmw, .refl⟩ (.nil _), rfl, rfl, rfl, rfl, rfl⟩

theorem bottom_sound {I : Type} {layer : Layer} (model : MemorySemantics)
    (initial : I → model.Initial) (admitted : I → Silmaril.X86.Concurrency.Sqlite.Execution model → Prop)
    (p : Projection layer model.Label model.Final) (allowed : I → layer.Input → Set Nat) :
    Sound model initial admitted p allowed ⊥ := fun _ impossible => False.elim impossible

theorem sound_downward {I : Type} {layer : Layer} {model : MemorySemantics}
    {initial : I → model.Initial} {admitted : I → Silmaril.X86.Concurrency.Sqlite.Execution model → Prop}
    {p : Projection layer model.Label model.Final} {allowed : I → layer.Input → Set Nat}
    {smaller larger : Proposal I layer} (included : smaller ⊆ larger)
    (sound : Sound model initial admitted p allowed larger) : Sound model initial admitted p allowed smaller :=
  fun pair hp => sound pair (included hp)

theorem sound_union {I : Type} {layer : Layer} {model : MemorySemantics}
    {initial : I → model.Initial} {admitted : I → Silmaril.X86.Concurrency.Sqlite.Execution model → Prop}
    {p : Projection layer model.Label model.Final} {allowed : I → layer.Input → Set Nat}
    {left right : Proposal I layer} (leftSound : Sound model initial admitted p allowed left)
    (rightSound : Sound model initial admitted p allowed right) : Sound model initial admitted p allowed (left ∪ right) := by
  intro pair included
  exact included.elim (leftSound pair) (rightSound pair)

end Silmaril.Proofs.X86.Concurrency.Sqlite.Release
