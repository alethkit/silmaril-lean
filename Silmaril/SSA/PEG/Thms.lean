module

public import Silmaril.SSA.PEG.Builder
public import Silmaril.SSA.PEG.Scope
import Silmaril.Proofs.SSA.PEG.Graph
import Silmaril.Proofs.SSA.PEG.Scope
import Silmaril.Proofs.SSA.PEG.Builder

public section

namespace Silmaril.SSA.PEG

universe u v w x y

variable {Data : Type u} {P : InstructionSet.{u,v} Data} {Q : InstructionSet.{u,w} Data}
variable {params results outputs : List (Ty Data)} {n n' l l' : Nat}

/-- Operand positions retain their sorts and are reindexed in place. -/
theorem Node.arg_relabel {s : Fin n → Ty Data} {out : Ty Data} {L L' : Type}
    (node : Node P params L s out) (f : InstructionMap P Q) (ids : Fin n' ≃ Fin n)
    (loops : L → L') (i : Fin node.inputs.length) :
    (node.relabel f ids loops).arg i = (node.arg i).reindex ids :=
  Proofs.arg_relabel node f ids loops i

theorem Graph.root_relabel (g : Graph P params results n l) (f : InstructionMap P Q)
    (ids : Fin n' ≃ Fin n) (loops : Fin l' ≃ Fin l) {out : Ty Data}
    (p : RVSDG.Port results out) :
    (g.relabel f ids loops).roots.get p = (g.roots.get p).reindex ids :=
  Proofs.root_relabel g f ids loops p

theorem Graph.mapOps_id (g : Graph P params results n l) : g.mapOps (fun op => op) = g :=
  Proofs.mapOps_id g

theorem Graph.mapOps_comp {R : InstructionSet.{u,y} Data} (g : Graph P params results n l)
    (f : InstructionMap P Q) (h : InstructionMap Q R) :
    (g.mapOps f).mapOps h = g.mapOps (fun op => h (f op)) :=
  Proofs.mapOps_comp g f h

theorem Graph.edge_relabel (g : Graph P params results n l) (f : InstructionMap P Q)
    (ids : Fin n' ≃ Fin n) (loops : Fin l' ≃ Fin l) (a b : Fin n') (k : EdgeKind (Fin l')) :
    (g.relabel f ids loops).Edge a k b ↔ g.Edge (ids a) (k.map loops) (ids b) :=
  Proofs.edge_relabel g f ids loops a b k

theorem Walk.map {V : Type u} {K : Type v} {V' : Type w} {K' : Type x}
    {e : V → K → V → Prop} {e' : V' → K' → V' → Prop}
    (f : V → V') (g : K → K') (step : ∀ {a b k}, e a k b → e' (f a) (g k) (f b))
    {a b : V} {ks : List K} (h : Walk e a ks b) : Walk e' (f a) (ks.map g) (f b) :=
  Proofs.mapWalk f g step h

theorem Walk.preserves {V : Type u} {K : Type v} {e : V → K → V → Prop}
    {a b : V} {ks : List K} (h : Walk e a ks b) {p : V → Prop}
    (step : ∀ {x y k}, e x k y → k ∈ ks → p x → p y) (ha : p a) : p b :=
  Proofs.walk_preserves h step ha

/-- A strict rank on the traversed edges rules out a nonempty cycle. -/
theorem Walk.strictRank {V : Type u} {K : Type v} {e : V → K → V → Prop}
    {a b : V} {ks : List K} (walk : Walk e a ks b) (nonempty : ks ≠ []) (rank : V → Nat)
    (step : ∀ {x y k}, e x k y → k ∈ ks → rank y < rank x) : rank b < rank a :=
  Proofs.walk_strictRank walk nonempty rank step

/-- Well-formedness is invariant under opcode relabelling and coherent
permutations of vertex and loop identifiers. Opcode maps may identify symbols. -/
theorem Graph.wellFormed_relabel (g : Graph P params results n l) (f : InstructionMap P Q)
    (ids : Fin n' ≃ Fin n) (loops : Fin l' ≃ Fin l) :
    (g.relabel f ids loops).WellFormed ↔ g.WellFormed :=
  Proofs.wellFormed_relabel g f ids loops

theorem Graph.wellFormed_reindex (g : Graph P params results n l)
    (ids : Fin n' ≃ Fin n) (loops : Fin l' ≃ Fin l) :
    (g.reindex ids loops).WellFormed ↔ g.WellFormed :=
  g.wellFormed_relabel (fun op => op) ids loops

theorem Graph.wellFormed_mapOps (g : Graph P params results n l) (f : InstructionMap P Q) :
    (g.mapOps f).WellFormed ↔ g.WellFormed :=
  g.wellFormed_relabel f (Equiv.refl _) (Equiv.refl _)

theorem Graph.wellFormed_withRoots (g : Graph P params results n l)
    (roots : RVSDG.Tuple (Ref g.sort) outputs) : (g.withRoots roots).WellFormed ↔ g.WellFormed :=
  ⟨fun h => ⟨h.forest, h.feedback, h.loopScope, h.outerFeedback⟩,
    fun h => ⟨h.forest, h.feedback, h.loopScope, h.outerFeedback⟩⟩

/-- The library's structural guard entails the three printed clauses. -/
theorem Graph.WellFormed.toPaper {g : Graph P params results n l} (wf : g.WellFormed) :
    g.PaperWellFormed :=
  Proofs.paperWellFormed_of_wellFormed g wf

variable [DecidableEq Data] {sort : Fin n → Ty Data} {ts : List (Ty Data)}

theorem checkRefs_roundTrip (rs : RVSDG.Tuple (Ref sort) ts) :
    checkRefs sort ts (refNumbers rs) = some rs :=
  Proofs.checkRefs_roundTrip rs

theorem checkRefs_numbers {is : List Nat} {rs : RVSDG.Tuple (Ref sort) ts}
    (h : checkRefs sort ts is = some rs) : refNumbers rs = is :=
  Proofs.checkRefs_numbers h

theorem Graph.check_roundTrip (g : Graph P params results n l) : g.toRaw.check = some g :=
  Proofs.check_roundTrip g

theorem RawGraph.toRaw_of_check {raw : RawGraph P params results n l} {g : Graph P params results n l}
    (h : raw.check = some g) : g.toRaw = raw :=
  Proofs.toRaw_of_check h

end Silmaril.SSA.PEG
