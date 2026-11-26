module

public import Silmaril.SSA.Peggy.Acyclic.Defs

/-! # Typed single-result PEGs and one-row extension -/

@[expose] public section

namespace Silmaril.SSA.Peggy.Optimizer

open RVSDG (Tuple)

variable {Data : Type} {P : PEG.InstructionSet.{0,0} Data}
variable {params : List (PEG.Ty Data)} {out : PEG.Ty Data} {n : Nat}

/-- A ranked loop-free table with its ordered output interface. -/
structure RankedProgram (P : PEG.InstructionSet.{0,0} Data)
    (params results : List (PEG.Ty Data)) where
  size : Nat
  graph : PEG.Graph P params results size 0
  ranked : Acyclic.Ranked graph

/-- The original root optimizer profiles one result. -/
abbrev Program (P : PEG.InstructionSet.{0,0} Data) (params : List (PEG.Ty Data))
    (out : PEG.Ty Data) := RankedProgram P params [out]

namespace Extension

def sorts (sort : Fin n → PEG.Ty Data) (out : PEG.Ty Data) : Fin (n + 1) → PEG.Ty Data :=
  Fin.cases out sort

def liftRef {sort : Fin n → PEG.Ty Data} {t : PEG.Ty Data} (out : PEG.Ty Data)
    (ref : PEG.Ref sort t) : PEG.Ref (sorts sort out) t :=
  ⟨ref.id.succ, ref.typed⟩

/-- Prepend a new result row. Every old edge is lifted by `Fin.succ`, and
the fresh row takes arguments only from old vertices. -/
def prepend (g : PEG.Graph P params [out] n 0) {ins : List (PEG.Ty Data)}
    (label : PEG.Label P params (Fin 0) ins out) (args : Tuple (PEG.Ref g.sort) ins) :
    PEG.Graph P params [out] (n + 1) 0 where
  forest := g.forest
  sort := sorts g.sort out
  node := Fin.cases (PEG.Node.ofLabel label (args.map fun _ => liftRef out))
    (fun i => PEG.Node.ofLabel (g.node i).label ((g.node i).args.map fun _ => liftRef out))
  roots := .cons ⟨0, rfl⟩ .nil

def prependRank (rank : Fin n → Nat) : Fin (n + 1) → Nat :=
  Fin.cases ((List.finRange n).foldr (fun i cap => max (rank i + 1) cap) 0) rank

/-- The same admission check is applied to the actual generated table. -/
def extend (p : Program P params out) {ins : List (PEG.Ty Data)}
    (label : PEG.Label P params (Fin 0) ins out) (args : Tuple (PEG.Ref p.graph.sort) ins) :
    Option (Program P params out) :=
  let g := prepend p.graph label args
  (Acyclic.Ranked.check g (prependRank p.ranked.rank)).map fun ranked => ⟨_, g, ranked⟩

end Extension
end Silmaril.SSA.Peggy.Optimizer
