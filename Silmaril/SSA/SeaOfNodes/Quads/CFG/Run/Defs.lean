module

public import Silmaril.SSA.SeaOfNodes.Quads.CFG.Defs

/-! # Executable terminators for topologically ordered quad CFGs -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.CFG

open RVSDG (Port)
open Diamond (ValueSort Signature Model dataPorts sortValue)
open Join (Block)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {n : Nat}

/-- The ordered quads of a block, addressed by its topological number. -/
def Graph.body : {n : Nat} → Graph Op regs n → Fin n → Block Op regs
  | _, .entry body => fun _ => body
  | _, .snoc prior _ body => Fin.lastCases body prior.body

/-- The initialized bank enters the first block. -/
def Graph.start : {n : Nat} → (graph : Graph Op regs n) → (i : Fin n) × Path graph i
  | _, .entry _ => ⟨0, .entry⟩
  | _, .snoc prior _ _ =>
    let start := prior.start
    ⟨start.1.castSucc, .earlier start.2⟩

/-- An outgoing edge references one position in a later block's incoming
list. The source index is exactly the predecessor found at that position. -/
inductive Edge : {n : Nat} → Graph Op regs n → Fin n → Type (max u v)
  | latest {n : Nat} {prior : Graph Op regs n} {preds : Predecessors n} {body : Block Op regs}
      (occurrence : Fin (preds.rest.length + 1)) :
      Edge (.snoc prior preds body) (preds.get occurrence).castSucc
  | earlier {n : Nat} {prior : Graph Op regs n} {preds : Predecessors n} {body : Block Op regs}
      {source : Fin n} (edge : Edge prior source) : Edge (.snoc prior preds body) source.castSucc

variable {graph : Graph Op regs n} {source : Fin n}

def Edge.target : {n : Nat} → {graph : Graph Op regs n} → {source : Fin n} →
    Edge graph source → Fin n
  | _, _, _, .latest _ => Fin.last _
  | _, _, _, .earlier edge => edge.target.castSucc

/-- The incoming position is preserved when the graph grows. -/
def Edge.slot : {n : Nat} → {graph : Graph Op regs n} → {source : Fin n} → Edge graph source → Nat
  | _, _, _, .latest occurrence => occurrence.val
  | _, _, _, .earlier edge => edge.slot

theorem Edge.forward (edge : Edge graph source) : source.val < edge.target.val := by
  induction edge with
  | latest occurrence => exact (Predecessors.get _ occurrence).isLt
  | earlier _ ih => exact ih

/-- Invert a path that ends before the most recently appended block. -/
def Path.beforeLatest {prior : Graph Op regs n} {preds : Predecessors n} {body : Block Op regs} :
    {j : Fin (n + 1)} → Path (.snoc prior preds body) j →
    (bound : j.val < n) → Path prior ⟨j.val, bound⟩
  | _, .earlier path, _ => path
  | _, .edge _ _, impossible => (Nat.lt_irrefl _ impossible).elim

def Path.unlift {prior : Graph Op regs n} {preds : Predecessors n} {body : Block Op regs}
    {i : Fin n} (path : Path (.snoc prior preds body) i.castSucc) : Path prior i :=
  path.beforeLatest i.isLt

/-- Realize exactly this occurrence as an extension of the checked path. -/
def Edge.take : {n : Nat} → {graph : Graph Op regs n} → {source : Fin n} →
    (edge : Edge graph source) → Path graph source → Path graph edge.target
  | _, _, _, .latest occurrence, path => .edge occurrence path.unlift
  | _, _, _, .earlier edge, path => .earlier (edge.take path.unlift)

/-- List the taken (successor block, incoming position) pairs in execution order. -/
def Path.occurrences : {n : Nat} → {graph : Graph Op regs n} → {i : Fin n} →
    Path graph i → List (Nat × Nat)
  | _, _, _, .entry => []
  | _, _, _, .earlier path => path.occurrences
  | _, _, _, .edge (n := priorSize) occurrence path => path.occurrences ++ [(priorSize, occurrence.val)]

/-- The conditional reads a predicate from the bank after the block's quads.
Parallel arms can share a successor and must use distinct incoming positions. -/
inductive Terminator (graph : Graph Op regs n) (source : Fin n) (out : ValueSort Data) where
  | jump (edge : Edge graph source)
  | branch (test : Port (dataPorts regs) (.value .predicate))
      (onTrue onFalse : Edge graph source) (distinct : onTrue ≠ onFalse)
  | ret (result : Port (dataPorts regs) (.value out))

def Terminator.edges : Terminator graph source out → List (Edge graph source)
  | .jump edge => [edge]
  | .branch _ onTrue onFalse _ => [onTrue, onFalse]
  | .ret _ => []

def Terminator.eval (m : Model.{u, v, w} Op) (bank : Bank m regs) :
    Terminator graph source out → sortValue m.value out ⊕ Edge graph source
  | .jump edge => .inr edge
  | .branch test onTrue onFalse _ => .inr (if (bank.get test).down then onTrue else onFalse)
  | .ret result => .inl (bank.get result)

/-- The terminators and incoming lists describe the same graph. Each
listed predecessor occurrence is named by its source's terminator. -/
structure Program (graph : Graph Op regs n) (out : ValueSort Data) where
  terminator : (source : Fin n) → Terminator graph source out
  covers : ∀ {source : Fin n} (edge : Edge graph source), edge ∈ (terminator source).edges

/-- A typed return and its actual checked control path. -/
structure Outcome (graph : Graph Op regs n) (m : Model.{u, v, w} Op) (out : ValueSort Data) where
  block : Fin n
  path : Path graph block
  result : sortValue m.value out

/-- Run from the post-body bank. Each transfer executes the selected
successor's quads exactly once, and its block number increases. -/
def Program.runFrom (program : Program graph out) (m : Model.{u, v, w} Op)
    (i : Fin n) (path : Path graph i) (bank : Bank m regs) : Outcome graph m out :=
  match (program.terminator i).eval m bank with
  | .inl result => ⟨i, path, result⟩
  | .inr edge => program.runFrom m edge.target (edge.take path) ((graph.body edge.target).eval m bank)
termination_by n - i.val
decreasing_by
  have forward := edge.forward
  have _bounded := edge.target.isLt
  omega

def Program.run (program : Program graph out) (m : Model.{u, v, w} Op)
    (input : Bank m regs) : Outcome graph m out :=
  let start := graph.start
  program.runFrom m start.1 start.2 ((graph.body start.1).eval m input)

/-- A path follows the source guards when every used occurrence is selected
by its predecessor's terminator evaluated on the source bank. -/
inductive Program.Follows (program : Program graph out) (m : Model.{u, v, w} Op)
    (input : Bank m regs) : {i : Fin n} → Path graph i → Prop
  | entry : Follows program m input graph.start.2
  | edge {i : Fin n} {path : Path graph i} (prior : Follows program m input path)
      (edge : Edge graph i)
      (taken : (program.terminator i).eval m (path.eval m input) = .inr edge) :
      Follows program m input (edge.take path)

def Program.Valid (program : Program graph out) (m : Model.{u, v, w} Op)
    (input : Bank m regs) (outcome : Outcome graph m out) : Prop :=
  program.Follows m input outcome.path ∧
    (program.terminator outcome.block).eval m (outcome.path.eval m input) = .inl outcome.result

end Silmaril.SSA.SeaOfNodes.Quads.CFG
