module

public import Silmaril.Proofs.SSA.PEG.Simple.Structured.Regions

public section

namespace Silmaril.SSA.PEG.Simple.Structured.Proofs

set_option backward.isDefEq.respectTransparency false

open RVSDG (Port Tuple)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params before middle after vars inside all : List (Ty Data)} {t : Ty Data}

@[expose] def top {n : Nat} (active : List (Region n)) : Option (Fin n) :=
  active.head?.map Region.pass

@[expose] def Visible {n : Nat} (catalog active : List (Region n)) (address : Nat) : Prop :=
  ∀ f ∈ catalog, f.Contains address → f ∈ active

@[expose] def AtRegions {n : Nat} (catalog active : List (Region n)) (address : Nat) : Prop :=
  ∀ f ∈ catalog, f.Contains address ↔ f ∈ active

theorem AtRegions.visible {n : Nat} {catalog active : List (Region n)} {a : Nat}
    (h : AtRegions catalog active a) : Visible catalog active a :=
  fun f mem inside => (h f mem).mp inside

/-- A code fragment occupies a contiguous band of new rows. Any region
from outside the fragment contains that whole band exactly when active. -/
structure Place (catalog active : List (Region all.length)) (code : Code P params before after) where
  embed : Embed after all
  offset : Nat
  address : AtOffset (fun r => embed r) offset
  localMem : ∀ f ∈ regions code embed offset (top active), f ∈ catalog
  activeEarlier : ∀ f ∈ active, f ∈ catalog ∧ f.pass.val < offset
  external : ∀ a, offset ≤ a → a < offset + width code →
    ∀ f ∈ catalog, f ∉ regions code embed offset (top active) → (f.Contains a ↔ f ∈ active)

variable {catalog active : List (Region all.length)}

theorem Place.exactAt {code : Code P params before after} (p : Place catalog active code)
    {a : Nat} (lo : p.offset ≤ a) (hi : a < p.offset + width code)
    (exclude : ∀ f ∈ regions code p.embed p.offset (top active), ¬f.Contains a) :
    AtRegions catalog active a := by
  classical
  intro f inCatalog
  by_cases localMem : f ∈ regions code p.embed p.offset (top active)
  · have bound := regionBounds code p.embed p.offset (top active) p.address f localMem
    refine ⟨fun h => (exclude f localMem h).elim, fun h => ?_⟩
    have earlier := (p.activeEarlier f h).2
    omega
  · exact p.external a lo hi f inCatalog localMem

@[expose] def Place.root (code : Code P params [] all) :
    Place (regions code (fun r => r) 0 none) [] code where
  embed := fun r => r
  offset := 0
  address := fun _ _ => (Nat.zero_add _).symm
  localMem := fun _ h => h
  activeEarlier := fun _ h => by cases h
  external := fun _ _ _ _ yes no => (no yes).elim

@[expose] def Place.left {a : Code P params before middle} {b : Code P params middle after}
    (p : Place catalog active (.seq a b)) : Place catalog active a where
  embed := fun r => p.embed (b.lift r)
  offset := p.offset + width b
  address := offsetLeft b p.embed p.offset p.address
  localMem := fun _ mem => p.localMem _ (List.mem_append_right _ mem)
  activeEarlier := fun f mem => ⟨(p.activeEarlier f mem).1, by have := (p.activeEarlier f mem).2; omega⟩
  external := by
    classical
    intro j lo hi f mem notLeft
    by_cases fromRight : f ∈ regions b p.embed p.offset (top active)
    · have h := regionBounds b p.embed p.offset (top active) p.address f fromRight
      have out : ¬f.Contains j := by
        intro over
        have := over.2
        omega
      have notActive : f ∉ active := by
        intro hA
        have := (p.activeEarlier f hA).2
        omega
      exact ⟨fun h => (out h).elim, fun h => (notActive h).elim⟩
    · refine p.external j (by omega) ?_ f mem ?_
      · change j < p.offset + (width b + width a)
        omega
      · intro contains
        exact (List.mem_append.mp contains).elim fromRight notLeft

@[expose] def Place.right {a : Code P params before middle} {b : Code P params middle after}
    (p : Place catalog active (.seq a b)) : Place catalog active b where
  embed := p.embed
  offset := p.offset
  address := p.address
  localMem := fun _ mem => p.localMem _ (List.mem_append_left _ mem)
  activeEarlier := p.activeEarlier
  external := by
    classical
    intro j lo hi f mem notRight
    by_cases fromLeft : f ∈ regions a (fun r => p.embed (b.lift r)) (p.offset + width b) (top active)
    · have h := regionBounds a (fun r => p.embed (b.lift r)) (p.offset + width b)
        (top active) (offsetLeft b p.embed p.offset p.address) f fromLeft
      have out : ¬f.Contains j := by
        intro over
        have := over.1
        omega
      have notActive : f ∉ active := by
        intro hA
        have := (p.activeEarlier f hA).2
        omega
      exact ⟨fun h => (out h).elim, fun h => (notActive h).elim⟩
    · refine p.external j lo ?_ f mem ?_
      · change j < p.offset + (width b + width a)
        omega
      · intro contains
        exact (List.mem_append.mp contains).elim notRight fromLeft

variable {init : Tuple (Port before) vars} {body : Code P params (vars ++ before) inside}
variable {guard : Port inside .bool} {next : Tuple (Port inside) vars} {neg : P [.bool] .bool}

@[expose] def Place.own (p : Place catalog active (.loop init body guard next neg)) : Region all.length :=
  region body p.embed p.offset (top active)

theorem Place.passPosition (p : Place catalog active (.loop init body guard next neg)) :
    p.own.pass.val = p.offset + vars.length :=
  regionPass body p.embed p.offset (top active) p.address

theorem Place.stopPosition (p : Place catalog active (.loop init body guard next neg)) :
    p.own.stop = p.offset + width (.loop init body guard next neg) := rfl

theorem Place.ownMem (p : Place catalog active (.loop init body guard next neg)) :
    p.own ∈ catalog :=
  p.localMem _ (.head _)

theorem Place.ownFresh (p : Place catalog active (.loop init body guard next neg)) :
    p.own ∉ active := by
  intro mem
  have earlier := (p.activeEarlier _ mem).2
  have pass := p.passPosition
  omega

@[expose] def Place.inner (p : Place catalog active (.loop init body guard next neg)) :
    Place catalog (p.own :: active) body where
  embed := fun r => p.embed (insideRef vars r)
  offset := p.offset + vars.length + 2
  address := offsetInner p.embed p.offset p.address
  localMem := fun _ mem => p.localMem _ (List.mem_cons_of_mem p.own mem)
  activeEarlier := by
    intro f mem
    rcases List.mem_cons.mp mem with rfl | old
    · refine ⟨p.ownMem, ?_⟩
      have := p.passPosition
      omega
    · obtain ⟨mem, earlier⟩ := p.activeEarlier f old
      exact ⟨mem, by omega⟩
  external := by
    classical
    intro j lo hi f mem notChild
    have atPass := p.passPosition
    have atStop := p.stopPosition
    change p.own.stop = p.offset + (vars.length + 2 + width body + vars.length) at atStop
    by_cases same : f = p.own
    · subst f
      exact ⟨fun _ => .head _, fun _ => ⟨by omega, by omega⟩⟩
    · rw [List.mem_cons, or_iff_right same]
      refine p.external j (by omega) ?_ f mem ?_
      · change j < p.offset + (vars.length + 2 + width body + vars.length)
        omega
      · intro contains
        exact (List.mem_cons.mp contains).elim same notChild

/-- A row on the loop's shell is in no child interval. Its membership in
the loop itself distinguishes the observers from negation and theta. -/
theorem Place.shell (p : Place catalog active (.loop init body guard next neg))
    {j : Nat} (lo : p.offset ≤ j) (hi : j < p.own.stop)
    (outsideChildren : j < p.inner.offset ∨ p.inner.offset + width body ≤ j) :
    ∀ f ∈ catalog, f.Contains j ↔
      (f = p.own ∧ p.own.Contains j) ∨ f ∈ active := by
  classical
  intro f mem
  by_cases own : f = p.own
  · subst f
    simp only [true_and, or_iff_left p.ownFresh]
  · rw [or_iff_right (fun h => own h.1)]
    by_cases child : f ∈ regions body p.inner.embed p.inner.offset (top (p.own :: active))
    · have bound := regionBounds body p.inner.embed p.inner.offset (top (p.own :: active))
        p.inner.address f child
      refine ⟨fun contains => ?_, fun member => ?_⟩
      · have left := contains.1
        have right := contains.2
        rcases outsideChildren with first | last <;> omega
      · have earlier := (p.activeEarlier f member).2
        have lower : p.offset ≤ p.inner.offset := by
          change p.offset ≤ p.offset + vars.length + 2
          omega
        omega
    · refine p.external j lo ?_ f mem ?_
      · rwa [← p.stopPosition]
      · intro localMem
        exact (List.mem_cons.mp localMem).elim own child

end Silmaril.SSA.PEG.Simple.Structured.Proofs
