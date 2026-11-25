module

public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Splice.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Thms

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Splice.Proofs

open OrderedRuntime.Structured (Ty Data Threaded runtime runtimePort nextRuntime newestIndex newestPort
  withRuntime readOrigin read_cons)
open Silmaril.Elgot (Iterate)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
variable {V : Type u} {P E : Dialect.{u,v} V PUnit.{u+1}}
variable {args input middle outs head : Ports (Ty V)}
variable {past target sigs after : List (Ports (Ty V))}
variable {t : Ty V} {F : Ty V → Type w}

private theorem read_older (head : Ports (Ty V)) (x : Tuple F head) :
    (past : List (Ports (Ty V))) → (i : Fin past.length) → (p : Port past[i] t) → (loc : Locals F past) →
    ((loc.snoc x).get (olderIndex head past i)).get (olderPort head past i p) = (loc.get i).get p
  | [], i => i.elim0
  | h :: past, i =>
    Fin.cases (motive := fun j => ∀ (p : Port (h :: past)[j] t) (loc : Locals F (h :: past)),
      ((loc.snoc x).get (olderIndex head (h :: past) j)).get
        (olderPort head (h :: past) j p) = (loc.get j).get p)
      (fun _ _ => rfl) (fun j p loc => read_older head x past j p loc.2) i

private theorem read_weak (src : Origin args past t) (entry : Tuple F args)
    (loc : Locals F past) (x : Tuple F head) :
    readOrigin (weaken head src) entry (loc.snoc x) = readOrigin src entry loc := by
  cases src with
  | arg => rfl
  | output i p => exact read_older head x past i p loc

private theorem read_newest (p : Port head t) (loc : Locals F past) (x : Tuple F head) :
    ((loc.snoc x).get (newestIndex head past)).get (newestPort p past) = x.get p := by
  induction past with
  | nil => rfl
  | cons _ _ ih => exact ih loc.2

private theorem read_split (head : Ports (Ty V)) (x : Tuple F head) :
    (past : List (Ports (Ty V))) → (i : Fin (past ++ [head]).length) →
    (p : Port (past ++ [head])[i] t) → (loc : Locals F past) →
      (match splitOutput head past i p with
      | .inl ⟨j, q⟩ => (loc.get j).get q
      | .inr q => x.get q) = ((loc.snoc x).get i).get p
  | [], i => by
    have eq : i = (0 : Fin 1) := @Subsingleton.elim (Fin 1) _ i 0
    subst i
    intro p loc
    rfl
  | h :: tail, i => by
    refine Fin.cases ?_ ?_ i
    · intro p loc
      rfl
    · intro j p loc
      have ih := read_split head x tail j p loc.2
      change _ = ((loc.2.snoc x).get j).get p
      simp only [splitOutput, Fin.cases_succ]
      cases key : splitOutput head tail j p with
      | inl s =>
        obtain ⟨k, q⟩ := s
        rw [key] at ih
        exact ih
      | inr q =>
        rw [key] at ih
        exact ih

private abbrev Reads (f : Routing input past args target)
    (oldEntry : Tuple F input) (oldLoc : Locals F past) (entry : Tuple F args) (loc : Locals F target) :=
  ∀ {t : Ty V} (src : Origin input past t), readOrigin (f src) entry loc = readOrigin src oldEntry oldLoc

private theorem push_reads {f : Routing input past args target}
    {oldEntry : Tuple F input} {oldLoc : Locals F past} {entry : Tuple F args} {loc : Locals F target}
    (reads : Reads f oldEntry oldLoc entry loc) (x : Tuple F head) :
    Reads (f.push head) oldEntry (oldLoc.snoc x) entry (loc.snoc x) := by
  intro t src
  cases src with
  | arg p => exact (read_weak (f (.arg p)) entry loc x).trans (reads (.arg p))
  | output i p =>
    have original := read_split head x past i p oldLoc
    cases key : splitOutput head past i p with
    | inl previous =>
      obtain ⟨j, q⟩ := previous
      simp only [Routing.push, key]
      rw [key] at original
      exact (read_weak (f (.output j q)) entry loc x).trans ((reads (.output j q)).trans original)
    | inr q =>
      simp only [Routing.push, key]
      rw [key] at original
      exact (read_newest q loc x).trans original

private theorem wires_read {f : Routing input past args target}
    {oldEntry : Tuple F input} {oldLoc : Locals F past} {entry : Tuple F args} {loc : Locals F target}
    (reads : Reads f oldEntry oldLoc entry loc) (xs : Wires input past outs) :
    (f.wires xs).read entry loc = xs.read oldEntry oldLoc := by
  induction xs with
  | nil => rfl
  | cons src rest ih =>
    change (Wires.read (.cons (f src) (f.wires rest)) entry loc) = _
    rw [read_cons, read_cons, reads, ih]

private theorem wires_runtime (f : Routing input past args target) (live : Origin input past runtime)
    (xs : Wires input past outs) :
    f.wires (withRuntime live xs) = withRuntime (f live) (f.wires xs) := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => exact congrArg (Tuple.cons _) ih

private theorem wire_get (xs : Wires args past input) (entry : Tuple F args) (loc : Locals F past)
    (p : Port input t) : (xs.read entry loc).get p = readOrigin (xs.get p) entry loc := by
  induction p with
  | head => cases xs; rw [read_cons]; rfl
  | tail p ih => cases xs with | cons _ rest => exact ih rest

private theorem boundary_reads (xs : Wires args past input) (entry : Tuple F args) (loc : Locals F past) :
    Reads (fromWires xs) (xs.read entry loc) PUnit.unit entry loc := by
  intro t src
  cases src with
  | arg p => exact (wire_get xs entry loc p).symm
  | output i _ => exact i.elim0

variable {M : Type (max u w) → Type (max u w)} [Monad M] [Iterate M]
variable (model : MonadicModel.{u,max u v,w} (OrderedRuntime.Structured.Opcode P E) M)

private theorem relocate_denote {a : Data input} {b : Data outs} {c : Data args}
    {live : Origin (Threaded input) past runtime}
    {term : Term (OrderedRuntime.Structured.Opcode P E) (Threaded input) past sigs (Threaded outs)}
    (check : Checked P E a b live term)
    (f : Routing (Threaded input) past (Threaded args) target)
    (oldEntry : Tuple model.Val (Threaded input)) (oldLoc : Locals model.Val past)
    (entry : Tuple model.Val (Threaded args)) (loc : Locals model.Val target)
    (reads : Reads f oldEntry oldLoc entry loc) :
    (relocate (c := c) f check).1.denoteOpenWith model entry loc = term.denoteOpenWith model oldEntry oldLoc := by
  induction check generalizing target with
  | ret live wires =>
    simp only [relocate, Term.denoteOpenWith, ← wires_runtime, wires_read reads]
  | primitive live i o op wires rest ih =>
    simp only [relocate, Term.denoteOpenWith, Node.ofBase, OrderedRuntime.Structured.primitiveNode,
      ← wires_runtime, wires_read reads]
    congr 1
    funext x
    exact ih (f.push _) oldEntry (oldLoc.snoc x) (loc.snoc x) (push_reads reads x)
  | gamma extra selector live i o wires sigs arms rest inner outer =>
    simp only [relocate, Term.denoteOpenWith, Node.ofBase, OrderedRuntime.Structured.gammaNode,
      ← wires_runtime, read_cons, wires_read reads, reads]
    congr 1
    funext x
    exact outer (f.push _) oldEntry (oldLoc.snoc x) (loc.snoc x) (push_reads reads x)
  | theta live i wires sigs body rest inner outer =>
    simp only [relocate, Term.denoteOpenWith, thetaNode, ← wires_runtime, wires_read reads]
    congr 1
    funext x
    exact outer (f.push _) oldEntry (oldLoc.snoc x) (loc.snoc x) (push_reads reads x)

variable [LawfulMonad M]

theorem append_denote {a : Data args} {b : Data middle} {c : Data outs}
    {first : Term (OrderedRuntime.Structured.Opcode P E) (Threaded args) past sigs (Threaded middle)}
    {second : Term (OrderedRuntime.Structured.Opcode P E) (Threaded middle) [] after (Threaded outs)}
    {live : Origin (Threaded args) past runtime} (producer : Checked P E a b live first)
    (consumer : EntryChecked (a := b) (b := c) second)
    (entry : Tuple model.Val (Threaded args)) (loc : Locals model.Val past) :
    (append consumer producer).1.denoteOpenWith model entry loc =
      first.denoteOpenWith model entry loc >>= fun mid => second.denoteOpenWith model mid PUnit.unit := by
  induction producer with
  | ret live wires =>
    simp only [append, Term.denoteOpenWith, pure_bind]
    exact relocate_denote model consumer _ _ _ _ _ (boundary_reads _ _ _)
  | primitive live i o op wires rest ih =>
    simp only [append, Term.denoteOpenWith, bind_assoc, ih]
  | gamma extra selector live i o wires sigs arms rest inner outer =>
    simp only [append, Term.denoteOpenWith, bind_assoc, outer]
  | theta live i wires sigs body rest inner outer =>
    simp only [append, Term.denoteOpenWith, bind_assoc, outer]

end Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Splice.Proofs
