module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Prefix.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Segment.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Proofs

open SeaOfNodes.Diamond (Model ValueSort)
open Join (Block)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable (p : Program src entry) (m : Model.{u, v, w} Op)

theorem outer_suffix_bank (incoming : Bank (regs := regs) m) :
    p.outerSuffixBank m incoming = p.outerSuffix.quads.eval m incoming :=
  Prefix.compiled_bank m _ incoming

theorem inner_edges_distinct : p.innerEdgeOccurrence true ≠ p.innerEdgeOccurrence false :=
  Prefix.inner_edges_distinct p.toRoutes
    (later := p.suffix.blocks ++ p.outerFalse.blocks ++ p.outerSuffix.blocks ++ [p.join, p.latch])
    (by simpa only [List.append_assoc] using p.distinct)

theorem outer_edges_distinct : p.outerEdgeOccurrence true ≠ p.outerEdgeOccurrence false := by
  have ordered := p.distinct
  simp only [List.append_assoc, List.cons_append, List.nil_append] at ordered
  have fromHeader := (List.nodup_cons.mp ordered).2
  have headerAbsent := (List.nodup_cons.mp fromHeader).1
  have arms := (List.nodup_cons.mp (List.nodup_cons.mp fromHeader).2).2
  have afterTrue := (List.nodup_append.mp arms).2.1
  have suffixAndLater := (List.nodup_append.mp afterTrue).2.1
  have separate := (List.nodup_append.mp suffixAndLater).2.2
  intro equal
  have samePred := congrArg Prod.fst equal
  change p.suffix.predecessor p.inner = p.outerFalse.predecessor p.header at samePred
  rcases Prefix.predecessor_mem p.suffix p.inner with ⟨empty, _⟩ | yes
  · exact p.nonempty empty
  rcases Prefix.predecessor_mem p.outerFalse p.header with ⟨_, direct⟩ | no
  · have headerIn : p.header ∈ p.suffix.blocks := (samePred.trans direct) ▸ yes
    exact headerAbsent (by simp [headerIn])
  · exact separate _ yes _ (List.mem_append_left _ no) samePred

theorem run_outer_suffix (incoming : Bank (regs := regs) m) (fuel : Nat) :
    src.runFrom m (fuel + p.outerSuffix.blocks.length) p.stop incoming =
      src.runFrom m fuel p.join (p.outerSuffixBank m incoming) := by
  rw [p.outerSuffix.run_segment m, outer_suffix_bank]

theorem run_to_merge (old : Bank (regs := regs) m) (fuel : Nat) :
    let occurrence := p.toControl.selected m old
    src.runFrom m (fuel + p.mergeVisits occurrence) p.header old =
      src.runFrom m fuel p.join (p.mergeBank m old occurrence) := by
  dsimp only
  rw [Program.mergeVisits, ← Nat.add_assoc, Nat.add_right_comm fuel (p.outerVisits (p.toControl.selected m old)),
    Prefix.run_to_outer p.toRoutes m old (fuel + p.outerSuffix.blocks.length), run_outer_suffix]
  rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Proofs
