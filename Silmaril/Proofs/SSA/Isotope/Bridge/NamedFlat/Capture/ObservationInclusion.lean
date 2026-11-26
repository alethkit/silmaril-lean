module

public import Silmaril.Semantics.ITree.Thms

/-! # Exact finite nodes compare their continuations by equality -/

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Capture

open Silmaril.Elgot.ITree (Tree Visible Approx vis vis_bind diverge ret)

private inductive CaptureEvent : Type → Type where
  | read : CaptureEvent Unit

private def replyDefined : Visible CaptureEvent Unit (Approx CaptureEvent Unit 1) → Prop
  | .ret _ => False
  | .vis .read next => (next ()).Dom

theorem exists_exact_observation_bind_counterexample :
    ∃ (Event : Type → Type) (producer : Tree Event Unit) (left right : Unit → Tree Event Unit),
      (∀ (reply : Unit) (depth : Nat) (node : Visible Event Unit (Approx Event Unit depth)),
        node ∈ (left reply).observe (depth + 1) → node ∈ (right reply).observe (depth + 1)) ∧
      ∃ (depth : Nat) (node : Visible Event Unit (Approx Event Unit depth)),
        node ∈ (producer >>= left).observe (depth + 1) ∧
          node ∉ (producer >>= right).observe (depth + 1) := by
  let produce : Tree CaptureEvent Unit := vis .read (fun reply => pure reply)
  let left : Unit → Tree CaptureEvent Unit := fun _ => diverge
  let right : Unit → Tree CaptureEvent Unit := fun _ => ret ()
  refine ⟨CaptureEvent, produce, left, right, ?_, 1, .vis .read (fun _ => Part.none), ?_, ?_⟩
  · intro reply depth node member
    exact (Part.notMem_none node member).elim
  · simp only [produce, vis_bind, pure_bind]
    exact Part.mem_some _
  · simp only [produce, vis_bind, pure_bind]
    intro member
    have same := Part.mem_some_iff.mp member
    have agrees := congrArg replyDefined same
    exact (Eq.mpr agrees trivial : False)

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Capture
