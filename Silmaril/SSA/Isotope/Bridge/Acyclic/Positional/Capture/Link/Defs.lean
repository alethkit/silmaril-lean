module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Complete.Thms

/-! # Serial linking of written captured tables -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Link

open Region (packedExitType)

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {d n m k l : Nat} {β : BoundCtx τ d} {L K : LCtx τ} {A : τ}
  {R : Fin k → τ} {S : Fin l → τ}

/-- Change the local and outward destinations together, leaving each
operand and its captures intact. -/
def mapTargets (f : ∀ {X}, Target R L X → Target S K X) : Block Φ β R L A → Block Φ β S K A
  | .jump a t => .jump a (f t)
  | .case a x y => .case a (f x) (f y)

def castTarget {X Y : τ} (h : X = Y) (t : Target R L X) : Target R L Y :=
  cast (congrArg (Target R L) h) t

def castBlock {X Y : τ} (h : X = Y) (b : Block Φ β R L X) : Block Φ β R L Y :=
  cast (congrArg (Block Φ β R L) h) b

variable (p : Table Φ β L n) (q : Table Φ β K m)

/-- Producer rows, one row per ordered handoff, and consumer rows occupy
disjoint intervals. -/
abbrev size (_ : Table Φ β L n) (_ : Table Φ β K m) := n + 1 + L.length + m

abbrev Index := Fin (size p q + 1)

def leftIndex (i : Fin (n + 1)) : Index p q := (i.castAdd L.length).castAdd (m + 1)
def handoffIndex (i : Fin L.length) : Index p q := (i.natAdd (n + 1)).castAdd (m + 1)
def rightIndex (i : Fin (m + 1)) : Index p q := i.natAdd (n + 1 + L.length)

def types : Index p q → τ :=
  Fin.addCases (m := n + 1 + L.length) (n := m + 1) (motive := fun _ => τ)
    (Fin.addCases (m := n + 1) (n := L.length) (motive := fun _ => τ) p.types L.get) q.types

@[simp] theorem left_type (i : Fin (n + 1)) : types p q (leftIndex p q i) = p.types i := by
  simp [types, leftIndex]

@[simp] theorem handoff_type (i : Fin L.length) : types p q (handoffIndex p q i) = L.get i := by
  simp [types, handoffIndex]

@[simp] theorem right_type (i : Fin (m + 1)) : types p q (rightIndex p q i) = q.types i := by
  simp [types, rightIndex]

omit [TypeFormers τ] in
theorem at_get (i : Fin L.length) : At L i.val (L.get i) := by
  exact List.getElem?_eq_getElem i.isLt

omit [TypeFormers τ] in
theorem at_lt {i : Nat} {X : τ} (h : At L i X) : i < L.length :=
  List.getElem?_eq_some_iff.mp h |>.1

omit [TypeFormers τ] in
theorem at_eq {i : Nat} {X : τ} (h : At L i X) : L.get ⟨i, at_lt h⟩ = X :=
  Option.some.inj ((at_get ⟨i, at_lt h⟩).symm.trans h)

def leftTarget : {A : τ} → Target p.types L A → Target (types p q) K A
  | _, .local i => castTarget (left_type p q i) (.local (leftIndex p q i))
  | _, .exit (i := i) h =>
    castTarget ((handoff_type p q ⟨i, at_lt h⟩).trans (at_eq h)) (.local (handoffIndex p q ⟨i, at_lt h⟩))

def rightTarget : {A : τ} → Target q.types K A → Target (types p q) K A
  | _, .local i => castTarget (right_type p q i) (.local (rightIndex p q i))
  | _, .exit h => .exit h

/-- Build the incoming packed tag before entering the consumer. The receiver
sees the shared ambient context and packed result, skipping the raw payload
binder introduced by the handoff. -/
def handoffOperand {B : τ} (a : Operand Φ (β.snoc (packedExitType L)) B) (i : Fin L.length) :
    Operand Φ (β.snoc (L.get i)) B :=
  let tagged := FiniteExit.tag L i.val (at_get i) (⟨.bv 0, .bv⟩ : Operand Φ (β.snoc (L.get i)) (L.get i))
  let receiver := a.2.rename ((BoundCtx.Renaming.succ β (L.get i)).up (packedExitType L))
  ⟨.let₁ tagged.1 _, .let₁ tagged.2 receiver⟩

variable (j : Fin (m + 1)) (a : Operand Φ (β.snoc (packedExitType L)) (q.types j))

def leftBlock (i : Fin (n + 1)) : Block Φ β (types p q) K (p.types i) :=
  mapTargets (leftTarget p q) (p.block i)

def handoffBlock (i : Fin L.length) : Block Φ β (types p q) K (L.get i) :=
  .jump (handoffOperand a i) (castTarget (right_type p q j) (.local (rightIndex p q j)))

def rightBlock (i : Fin (m + 1)) : Block Φ β (types p q) K (q.types i) :=
  mapTargets (rightTarget p q) (q.block i)

/-- Link the two original tables and the handoff rows in one written CFG. -/
def table : Table Φ β K (size p q) where
  types := types p q
  block :=
    Fin.addCases (m := n + 1 + L.length) (n := m + 1)
      (motive := fun i => Block Φ β (types p q) K (types p q i))
      (Fin.addCases (m := n + 1) (n := L.length)
        (fun i => castBlock (left_type p q i).symm (leftBlock p q i))
        (fun i => castBlock (handoff_type p q i).symm (handoffBlock p q j a i)))
      (fun i => castBlock (right_type p q i).symm (rightBlock p q i))

def entry (i : Fin (n + 1)) (start : Operand Φ β (p.types i)) :
    Operand Φ β ((table p q j a).types (leftIndex p q i)) :=
  cast (congrArg (Operand Φ β) (left_type p q i).symm) start

/-- Native LetCase sequencing evaluates the producer once, then evaluates
the consumer entry under the packed result binder. The consumer rows read
the shared captures and their current packet. -/
def continuation (hq : q.check = true) : Operand Φ (β.snoc (packedExitType L)) (packedExitType K) :=
  (.join (.br a) ((Reverse.tableTree q hq j).render (.skip .base (packedExitType L)))
    : FiniteExit Φ K (β.snoc (packedExitType L))).encode.toLetCase

/-- Plug an exact producer computation into the bound input of a continuation. -/
def bind (a : Operand Φ β (packedExitType L))
    (b : Operand Φ (β.snoc (packedExitType L)) (packedExitType K)) :
    Operand Φ β (packedExitType K) :=
  ⟨.let₁ a.1 b.1, .let₁ a.2 b.2⟩

/-- The written identity dispatches its input tag directly to the matching
outward position. The empty tail is impossible. -/
def identityTree : {L : LCtx τ} → L ≠ [] → Reverse.Tree Φ β L (packedExitType L)
  | [], h => (h rfl).elim
  | X :: R, _ => Reverse.decoder (rfl : At (X :: R) 0 X) (X :: R) .here

def identityTable (h : L ≠ []) : Table Φ β L ((identityTree (Φ := Φ) (β := β) h).build .empty).labels.length :=
  ((identityTree h).build .empty).plan.toTable

open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural in
/-- Native LetCase substitution on equation classes, defined by its let
binder and native congruence. -/
def operandClass {Φ : Type} [LetCase.Structural.Finite.Signature Φ] {d : Nat}
    {β : BoundCtx (Ty Empty) d} {L K : LCtx (Ty Empty)}
    (receiver : Operand Φ (β.snoc (packedExitType L)) (packedExitType K)) :
    Quotient (Reverse.operandSetoid Φ β L) → Quotient (Reverse.operandSetoid Φ β K) :=
  Quotient.map (fun producer => bind producer receiver)
    (fun {_ _} left => LetCase.LocallyNameless.Equiv.let₁ left (.refl receiver.2.toHasType))

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Link
