module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.FiniteExit.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Thms

/-! # Forward positional SSA tables with payload-only blocks -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional

open Silmaril.SSA.RVSDG.LambdaSSA
open LinearChain (Site localSite)

universe u

variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]

/-- A single positional CFG table. Blocks may jump or case on a primitive
applied to their own parameter. Local targets may have multiple predecessors. -/
structure Table (Φ : Type u) [HasTy Φ τ] (L : LCtx τ) (n : Nat) where
  types : Fin n → τ
  block : ∀ i, Acyclic.Block Φ (List.ofFn types ++ L) (types i)

variable {L : LCtx τ} {n : Nat}

/-- Use the existing block target enumeration to check the supplied numbering.
All local edges strictly increase. External labels follow the locals. -/
def Table.check (p : Table Φ L n) : Bool :=
  (List.finRange n).all fun i => (p.block i).targets.all fun j => decide (i.val < j)

/-- A successful check certifies every edge, including edges of unreachable blocks. -/
abbrev Table.Forward (p : Table Φ L n) : Prop := p.check = true

/-- Names in the native CFG have the local prefix followed by the ordered exits. -/
def Table.toSSA (p : Table Φ L n) {d : Nat} {β : BoundCtx τ d} (i : Fin n)
    (a : Operand Φ β (p.types i)) : Region Φ :=
  .cfg (.br i (Morphism.CaseSSA.erase a.1)) n (fun j => (p.block j).region)

theorem Table.toSSA_hasType (p : Table Φ L n) {d : Nat} {β : BoundCtx τ d} (i : Fin n)
    (a : Operand Φ β (p.types i)) : Region.HasType β.toList (p.toSSA i a) L :=
  .cfg p.types (.br (localSite p.types L i).typing (Morphism.CaseSSA.erase_hasType a.2.toHasType))
    (fun j => (p.block j).typing β.toList)

/-- Split a native target at the local/external boundary, retaining its payload type. -/
inductive Destination (p : Table Φ L n) (A : τ) where
  | local (i : Fin n) (ty : p.types i = A)
  | exit (j : Nat) (ty : At L j A)

/-- Classify a typed target by its position in the appended interface. -/
def Table.destination (p : Table Φ L n) {A : τ}
    (s : Site (List.ofFn p.types ++ L) A) : Destination p A :=
  if h : s.index < n then
    .local ⟨s.index, h⟩ (by
      have ty := s.typing
      change (List.ofFn p.types ++ L)[s.index]? = some A at ty
      rw [List.getElem?_append_left (by simpa using h)] at ty
      simpa [List.getElem?_eq_getElem, h] using ty)
  else
    .exit (s.index - n) (by
      have ty := s.typing
      change (List.ofFn p.types ++ L)[s.index]? = some A at ty
      rw [List.getElem?_append_right (by simpa using Nat.le_of_not_gt h)] at ty
      simpa only [List.length_ofFn] using ty)

/-- Apply a typed unary primitive to the newest payload. -/
def operand {d : Nat} {β : BoundCtx τ d} {A B : τ} (op : TwoBlock.Instruction Φ A B) :
    Operand Φ (β.snoc A) B := by
  obtain ⟨f, input, output⟩ := op
  subst A B
  exact ⟨.op f (.bv 0), .op .bv⟩

def Destination.index {p : Table Φ L n} {A : τ} : Destination p A → Nat
  | .local i _ => i.val
  | .exit j _ => n + j

theorem Table.destination_index (p : Table Φ L n) {A : τ}
    (s : Site (List.ofFn p.types ++ L) A) : (p.destination s).index = s.index := by
  unfold Table.destination
  split
  · rfl
  · rename_i h
    change n + (s.index - n) = s.index
    omega

theorem Table.forward_iff (p : Table Φ L n) :
    p.Forward ↔ ∀ i, ∀ j ∈ (p.block i).targets, i.val < j := by
  simp [Table.Forward, Table.check, List.all_eq_true]

/-- Reuse the existing ordered compiler's native block table. -/
def Table.ofCompiled {A : τ} (p : Acyclic.Compiled Φ L A) :
    Table Φ L (p.rest.locals.length + 1) :=
  ⟨p.localTypes, p.blockAt⟩

/-- The existing compiler's forward-edge theorem discharges this checker. -/
theorem Table.ofCompiled_forward {A : τ} (p : Acyclic.Compiled Φ L A) :
    (Table.ofCompiled p).Forward :=
  (Table.ofCompiled p).forward_iff.mpr p.blockAt_forward

/-- A continuation is valid under any captured context. Source blocks never read
this context; it can grow as the lowering binds intermediate payloads. -/
abbrev Later (p : Table Φ L n) (i : Fin n) :=
  ∀ (j : Fin n), i.val < j.val → ∀ {d : Nat} (β : BoundCtx τ d),
    FiniteExit Φ L (β.snoc (p.types j))

def Table.compileDestination (p : Table Φ L n) (i : Fin n) {A : τ}
    (target : Destination p A) (forward : i.val < target.index) {d : Nat} (β : BoundCtx τ d)
    (later : Later p i) : FiniteExit Φ L (β.snoc A) :=
  match target with
  | .local j ty => ty ▸ later j forward β
  | .exit _ ty => .br ty ⟨.bv 0, .bv⟩

def Table.compileTarget (p : Table Φ L n) (i : Fin n) {A : τ}
    (s : Site (List.ofFn p.types ++ L) A) (forward : i.val < s.index) {d : Nat} (β : BoundCtx τ d)
    (later : Later p i) : FiniteExit Φ L (β.snoc A) :=
  p.compileDestination i (p.destination s) ((p.destination_index s).symm ▸ forward) β later

def Table.compileBlock (p : Table Φ L n) (i : Fin n)
    (b : Acyclic.Block Φ (List.ofFn p.types ++ L) (p.types i))
    (forward : ∀ j ∈ b.targets, i.val < j) {d : Nat} (β : BoundCtx τ d)
    (later : Later p i) : FiniteExit Φ L (β.snoc (p.types i)) :=
  match b with
  | .jump op s =>
    .join (.br (operand op)) (p.compileTarget i s (forward _ (by simp [Acyclic.Block.targets]))
      (β.snoc (p.types i)) later)
  | .branch op l r =>
    .case (operand op)
      (p.compileTarget i l (forward _ (by simp [Acyclic.Block.targets])) (β.snoc (p.types i)) later)
      (p.compileTarget i r (forward _ (by simp [Acyclic.Block.targets])) (β.snoc (p.types i)) later)

/-- Unfold the forward table into structured continuations. Shared blocks may
appear in more than one syntactic branch. -/
def Table.compileAt (p : Table Φ L n) (ok : p.Forward) (i : Fin n) {d : Nat}
    (β : BoundCtx τ d) : FiniteExit Φ L (β.snoc (p.types i)) :=
  p.compileBlock i (p.block i) (p.forward_iff.mp ok i) β
    (fun j _ _ γ => p.compileAt ok j γ)
termination_by n - i.val
decreasing_by omega

/-- Evaluate the entry operand, then use its value once as the first block
parameter. The output interface is the original ordered list of exits. -/
def Table.toFiniteExit (p : Table Φ L n) (ok : p.Forward) {d : Nat} {β : BoundCtx τ d} (i : Fin n)
    (a : Operand Φ β (p.types i)) : FiniteExit Φ L β :=
  .join (.br a) (p.compileAt ok i β)

/-- Use the finite-exit bridge to produce exact LetCase. -/
def Table.toLetCase (p : Table Φ L n) (ok : p.Forward) {d : Nat} {β : BoundCtx τ d} (i : Fin n)
    (a : Operand Φ β (p.types i)) : Operand Φ β (Region.packedExitType L) :=
  (p.toFiniteExit ok i a).encode.toLetCase

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional
