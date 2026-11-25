module

public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Splice.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Thms
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.ExplicitRuntime.Splice.Execution

/-! # Denotation and finite returns of a checked numbered splice -/

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Splice

open OrderedRuntime.Structured (Ty Data Threaded runtime Opcode)
open Silmaril.Elgot (Iterate)

universe u v w
variable {V : Type u} {P E : Dialect.{u,v} V PUnit.{u+1}}
variable {args middle outs : Ports (Ty V)}
variable {past sigs after : List (Ports (Ty V))}
variable {a : Data args} {b : Data middle} {c : Data outs}
variable {M : Type (max u w) → Type (max u w)} [Monad M] [LawfulMonad M] [Iterate M]

theorem append_denote (model : MonadicModel.{u,max u v,w} (Opcode P E) M)
    {first : Term (Opcode P E) (Threaded args) past sigs (Threaded middle)}
    {second : Term (Opcode P E) (Threaded middle) [] after (Threaded outs)}
    {live : Origin (Threaded args) past runtime} (producer : Checked P E a b live first)
    (consumer : EntryChecked (a := b) (b := c) second)
    (entry : Tuple model.Val (Threaded args)) (loc : Locals model.Val past) :
    (append consumer producer).1.denoteOpenWith model entry loc =
      first.denoteOpenWith model entry loc >>= fun mid => second.denoteOpenWith model mid PUnit.unit :=
  Proofs.append_denote model producer consumer entry loc

/-- The actual numbered graph observes the producer, then the consumer at
the producer's full returned tuple. -/
theorem graph_observe (model : Partial.Model.{u,max u v,w} (Opcode P E))
    {first : Graph (Opcode P E) (Threaded args) [] sigs (Threaded middle)}
    {second : Graph (Opcode P E) (Threaded middle) [] after (Threaded outs)}
    (producer : EntryChecked (a := a) (b := b) first.toTerm)
    (consumer : EntryChecked (a := b) (b := c) second.toTerm)
    (entry : Tuple model.Val (Threaded args)) :
    Partial.observe model (graph producer consumer) entry =
      Partial.observe model first entry >>= Partial.observe model second := by
  simp only [Partial.observe, graph, Term.toTerm_toGraph]
  exact append_denote model producer consumer entry PUnit.unit

/-- A finite execution of the numbered splice has a finite execution of
each component with exactly matching boundary wires. -/
theorem graph_returns_iff (model : Partial.Model.{u,max u v,w} (Opcode P E))
    {first : Graph (Opcode P E) (Threaded args) [] sigs (Threaded middle)}
    {second : Graph (Opcode P E) (Threaded middle) [] after (Threaded outs)}
    (producer : EntryChecked (a := a) (b := b) first.toTerm)
    (consumer : EntryChecked (a := b) (b := c) second.toTerm)
    (entry : Tuple model.Val (Threaded args)) (output : Tuple model.Val (Threaded outs)) :
    Partial.returns model (graph producer consumer) entry output ↔
      ∃ boundary, Partial.returns model first entry boundary ∧ Partial.returns model second boundary output := by
  rw [← Partial.observe_eq_some, graph_observe, Part.eq_some_iff, Part.bind_eq_bind, Part.mem_bind_iff]
  simp only [← Part.eq_some_iff, Partial.observe_eq_some]

end Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Splice
