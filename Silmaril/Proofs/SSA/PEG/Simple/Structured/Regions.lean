module

public import Silmaril.Proofs.SSA.PEG.Simple.Structured.Guard

public section

namespace Silmaril.SSA.PEG.Simple.Structured.Proofs

set_option backward.isDefEq.respectTransparency false

open RVSDG (Port Tuple)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params before after vars inside all middle : List (Ty Data)} {t : Ty Data}

/-- The pass address precedes the open interval of nodes inside its loop.
The upper bound is the first address of the pre-loop table. -/
structure Region (n : Nat) where
  pass : Fin n
  stop : Nat
  parent : Option (Fin n)

@[expose] def Region.Contains {n : Nat} (r : Region n) (address : Nat) : Prop :=
  r.pass.val < address ∧ address < r.stop

@[expose] def region (body : Code P params (vars ++ before) inside)
    (embed : Embed (vars ++ .count :: .bool :: inside) all) (offset : Nat)
    (parent : Option (Fin all.length)) : Region all.length :=
  ⟨(numberPort (embed (passRef vars))).id, offset + (vars.length + 2 + width body + vars.length), parent⟩

@[expose] def regions :
    {before after : List (Ty Data)} → Code P params before after → Embed after all →
    Nat → Option (Fin all.length) → List (Region all.length)
  | _, _, .straight _, _, _, _ => []
  | _, _, .seq a b, embed, offset, parent =>
    regions b embed offset parent ++ regions a (fun r => embed (b.lift r)) (offset + width b) parent
  | _, _, .loop (vars := vars) _ body _ _ _, embed, offset, parent =>
    let own := region body embed offset parent
    own :: regions body (fun r => embed (insideRef vars r)) (offset + vars.length + 2) (some own.pass)

abbrev AtOffset (embed : Embed after all) (offset : Nat) :=
  ∀ t (r : Port after t), pos (embed r) = offset + pos r

theorem offsetLeft (b : Code P params middle after)
    (embed : Embed after all) (offset : Nat) (h : AtOffset (fun r => embed r) offset) :
    AtOffset (fun r => embed (b.lift r)) (offset + width b) := by
  intro t r
  rw [h, liftPosition, Nat.add_assoc]

theorem offsetInner
    (embed : Embed (vars ++ .count :: .bool :: inside) all) (offset : Nat)
    (h : AtOffset (fun r => embed r) offset) :
    AtOffset (fun r => embed (insideRef vars r)) (offset + vars.length + 2) := by
  intro t r
  rw [h, posInside]
  omega

theorem regionPass (body : Code P params (vars ++ before) inside)
    (embed : Embed (vars ++ .count :: .bool :: inside) all) (offset : Nat)
    (parent : Option (Fin all.length)) (address : AtOffset (fun r => embed r) offset) :
    (region body embed offset parent).pass.val = offset + vars.length := by
  change pos (embed (passRef vars)) = _
  rw [address, posPass]

theorem regionBounds (code : Code P params before after) (embed : Embed after all)
    (offset : Nat) (parent : Option (Fin all.length)) (address : AtOffset (fun r => embed r) offset)
    (f : Region all.length) (mem : f ∈ regions code embed offset parent) :
    offset ≤ f.pass.val ∧ f.pass.val < f.stop ∧ f.stop ≤ offset + width code := by
  induction code generalizing offset parent with
  | straight code => cases mem
  | seq a b ihA ihB =>
    change f ∈ regions b embed offset parent ++
      regions a (fun r => embed (b.lift r)) (offset + width b) parent at mem
    change _ ∧ _ ∧ f.stop ≤ offset + (width b + width a)
    rcases List.mem_append.mp mem with right | left
    · have h := ihB embed offset parent address right
      omega
    · have h := ihA (fun r => embed (b.lift r)) (offset + width b) parent
        (offsetLeft b embed offset address) left
      omega
  | @loop before vars inside init body guard next neg ih =>
    let own := region body embed offset parent
    change f ∈ own :: regions body (fun r => embed (insideRef vars r))
      (offset + vars.length + 2) (some own.pass) at mem
    change _ ∧ _ ∧ f.stop ≤ offset + (vars.length + 2 + width body + vars.length)
    rcases List.mem_cons.mp mem with rfl | child
    · have h := regionPass body embed offset parent address
      change offset ≤ (region body embed offset parent).pass.val ∧
        (region body embed offset parent).pass.val < offset + (vars.length + 2 + width body + vars.length) ∧ _
      rw [h]
      exact ⟨by omega, by omega, Nat.le_refl _⟩
    · have h := ih (fun r => embed (insideRef vars r)) (offset + vars.length + 2)
        (some own.pass) (offsetInner embed offset address) child
      omega

/-- Each listed region is anchored by a pass row in the actual table. -/
theorem regionOrigin (code : Code P params before after) (holes : Rows P params before all)
    (embed : Embed after all) (offset : Nat) (parent : Option (Fin all.length))
    (f : Region all.length) (mem : f ∈ regions code embed offset parent) :
    ∃ r : Port after .count, (numberPort (embed r)).id = f.pass ∧
      (code.rows holes embed parent r).parent = f.parent := by
  induction code generalizing offset parent with
  | straight code => cases mem
  | seq a b ihA ihB =>
    change f ∈ regions b embed offset parent ++
      regions a (fun r => embed (b.lift r)) (offset + width b) parent at mem
    rcases List.mem_append.mp mem with right | left
    · exact ihB _ embed offset parent right
    · obtain ⟨r, id, row⟩ := ihA holes (fun r => embed (b.lift r)) (offset + width b) parent left
      refine ⟨b.lift r, id, ?_⟩
      rw [Code.rows, rows_lift]
      exact row
  | @loop before vars inside init body guard next neg ih =>
    let own := region body embed offset parent
    change f ∈ own :: regions body (fun r => embed (insideRef vars r))
      (offset + vars.length + 2) (some own.pass) at mem
    rcases List.mem_cons.mp mem with same | child
    · subst f
      refine ⟨passRef vars, rfl, ?_⟩
      rw [Code.rows, loopRows_pass]
      rfl
    · obtain ⟨r, id, row⟩ := ih (loopHoles body init next holes embed) (fun r => embed (insideRef vars r))
        (offset + vars.length + 2) (some own.pass) child
      refine ⟨insideRef vars r, id, ?_⟩
      rw [Code.rows, loopRows_inside]
      exact row

theorem portLookup {X : Type} (get : ∀ {t}, Port all t → X) (r : Port all t) :
    get (portAt all (numberPort r).id) = get r := by
  induction r with
  | head => rfl
  | tail r ih => exact ih (fun p => get (.tail p))

theorem regionParent (code : Code P params [] all) {outs : List (Ty Data)}
    (roots : Tuple (Port all) outs) {f : Region all.length}
    (mem : f ∈ regions code (fun r => r) 0 none) :
    (code.toGraph roots).forest.parent f.pass = f.parent := by
  obtain ⟨r, id, row⟩ := regionOrigin code (fun r => nomatch r) (fun r => r) 0 none f mem
  rw [← id]
  exact (portLookup (code.rows (fun p => nomatch p) (fun p => p) none · |>.parent) r).trans row

def ParentOf {n : Nat} (catalog : List (Region n)) (inner : Fin n) (_ : Unit) (outer : Fin n) : Prop :=
  ∃ f ∈ catalog, f.pass = inner ∧ f.parent = some outer

theorem walkMono {V : Type} {K : Type} {e f : V → K → V → Prop}
    (step : ∀ {a b k}, e a k b → f a k b) {a b : V} {ks : List K}
    (walk : Walk e a ks b) : Walk f a ks b := by
  induction walk with
  | nil a => exact .nil a
  | cons edge _ ih => exact .cons (step edge) ih

private theorem liftParentWalk {n : Nat} {localCatalog catalog : List (Region n)}
    (contains : ∀ f ∈ localCatalog, f ∈ catalog)
    {i j : Fin n} {ks : List Unit} (walk : Walk (ParentOf localCatalog) i ks j) :
    Walk (ParentOf catalog) i ks j :=
  walkMono (fun ⟨f, mem, h⟩ => ⟨f, contains f mem, h⟩) walk

private theorem extendWalk {n : Nat} {rel : Fin n → Unit → Fin n → Prop}
    {i j k : Fin n} {ks : List Unit} (walk : Walk rel i ks j) (last : rel j () k) :
    Walk rel i (ks ++ [()]) k := by
  induction walk with
  | nil => exact .cons last (.nil _)
  | cons edge _ ih => exact .cons edge (ih last)

private theorem reachesParent (code : Code P params before after) (embed : Embed after all)
    (off : Nat) (parent : Fin all.length) {f : Region all.length}
    (mem : f ∈ regions code embed off (some parent)) :
    ∃ ks, Walk (ParentOf (regions code embed off (some parent))) f.pass ks parent ∧ ks ≠ [] := by
  induction code generalizing off parent with
  | straight _ => cases mem
  | seq a b ihA ihB =>
    change f ∈ regions b embed off (some parent) ++
      regions a (fun r => embed (b.lift r)) (off + width b) (some parent) at mem
    rcases List.mem_append.mp mem with right | left
    · obtain ⟨ks, path, positive⟩ := ihB embed off parent right
      exact ⟨ks, liftParentWalk (fun _ h => List.mem_append_left _ h) path, positive⟩
    · obtain ⟨ks, path, positive⟩ := ihA (fun r => embed (b.lift r)) (off + width b) parent left
      exact ⟨ks, liftParentWalk (fun _ h => List.mem_append_right _ h) path, positive⟩
  | @loop before vars inside init body guard next neg ih =>
    let own := region body embed off (some parent)
    let inner := regions body (fun r => embed (insideRef vars r)) (off + vars.length + 2) (some own.pass)
    change f ∈ own :: inner at mem
    have up : ParentOf (own :: inner) own.pass () parent := ⟨own, .head _, rfl, rfl⟩
    rcases List.mem_cons.mp mem with rfl | child
    · exact ⟨[()], .cons up (.nil _), by simp⟩
    · obtain ⟨ks, path, _⟩ := ih (fun r => embed (insideRef vars r)) (off + vars.length + 2) own.pass child
      have complete := extendWalk (liftParentWalk (fun _ h => List.mem_cons_of_mem own h) path) up
      exact ⟨ks ++ [()], complete, by simp⟩

/-- A second pass in the open interval of a loop is a strict descendant. -/
theorem regionAncestry (code : Code P params before after)
    (embed : Embed after all) (off : Nat) (parent : Option (Fin all.length))
    (addr : AtOffset (fun r => embed r) off)
    (outer inner : Region all.length)
    (hasOuter : outer ∈ regions code embed off parent) (hasInner : inner ∈ regions code embed off parent)
    (contained : outer.Contains inner.pass.val) :
    ∃ ks, Walk (ParentOf (regions code embed off parent)) inner.pass ks outer.pass ∧ ks ≠ [] := by
  induction code generalizing off parent with
  | straight _ => cases hasOuter
  | seq a b ihA ihB =>
    let R := regions b embed off parent
    let L := regions a (fun r => embed (b.lift r)) (off + width b) parent
    change outer ∈ R ++ L at hasOuter
    change inner ∈ R ++ L at hasInner
    have newAddr := offsetLeft b embed off addr
    rcases List.mem_append.mp hasOuter with oR | oL <;>
      rcases List.mem_append.mp hasInner with iR | iL
    · obtain ⟨ks, walk, ne⟩ := ihB embed off parent addr oR iR
      exact ⟨ks, liftParentWalk (fun _ h => List.mem_append_left _ h) walk, ne⟩
    · have hO := regionBounds b embed off parent addr outer oR
      have hI := regionBounds a (fun r => embed (b.lift r)) (off + width b) parent newAddr inner iL
      have lt := contained.2
      omega
    · have hO := regionBounds a (fun r => embed (b.lift r)) (off + width b) parent newAddr outer oL
      have hI := regionBounds b embed off parent addr inner iR
      have lt := contained.1
      omega
    · obtain ⟨ks, walk, ne⟩ := ihA (fun r => embed (b.lift r)) (off + width b) parent newAddr oL iL
      exact ⟨ks, liftParentWalk (fun _ h => List.mem_append_right _ h) walk, ne⟩
  | @loop before vars inside init body guard next neg ih =>
    let own := region body embed off parent
    let sub := regions body (fun r => embed (insideRef vars r)) (off + vars.length + 2) (some own.pass)
    change outer ∈ own :: sub at hasOuter
    change inner ∈ own :: sub at hasInner
    have innerAddr := offsetInner embed off addr
    rcases List.mem_cons.mp hasOuter with rfl | o <;> rcases List.mem_cons.mp hasInner with rfl | i
    · exact (Nat.lt_irrefl _ contained.1).elim
    · obtain ⟨ks, walk, ne⟩ := reachesParent body (fun r => embed (insideRef vars r))
        (off + vars.length + 2) own.pass i
      exact ⟨ks, liftParentWalk (fun _ h => List.mem_cons_of_mem own h) walk, ne⟩
    · have h := regionBounds body (fun r => embed (insideRef vars r)) (off + vars.length + 2)
        (some own.pass) innerAddr outer o
      have atPass : own.pass.val = off + vars.length := regionPass body embed off parent addr
      have lt := contained.1
      omega
    · obtain ⟨ks, walk, ne⟩ := ih (fun r => embed (insideRef vars r)) (off + vars.length + 2)
        (some own.pass) innerAddr o i
      exact ⟨ks, liftParentWalk (fun _ h => List.mem_cons_of_mem own h) walk, ne⟩

theorem actualAncestry (code : Code P params [] all) {outs : List (Ty Data)}
    (roots : Tuple (Port all) outs) {outer inner : Region all.length}
    (outerMem : outer ∈ regions code (fun r => r) 0 none)
    (innerMem : inner ∈ regions code (fun r => r) 0 none)
    (inside : outer.Contains inner.pass.val) :
    (code.toGraph roots).forest.StrictlyEncloses outer.pass inner.pass := by
  obtain ⟨ks, walk, ne⟩ := regionAncestry code (fun r => r) 0 none (fun _ _ => (Nat.zero_add _).symm)
    outer inner outerMem innerMem inside
  refine ⟨ks, walkMono ?_ walk, ne⟩
  intro a b k edge
  obtain ⟨f, mem, rfl, parent⟩ := edge
  exact (regionParent code roots mem).trans parent

end Silmaril.SSA.PEG.Simple.Structured.Proofs
