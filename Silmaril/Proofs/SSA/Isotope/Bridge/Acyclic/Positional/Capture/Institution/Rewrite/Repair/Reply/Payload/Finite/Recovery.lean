module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Replay

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite

theorem traceTree_inj_proof {L : List Sorts} {n : Nat} (p : Normal L n) :
    ∀ q : Normal L n, (∀ env, p.traceTree env = q.traceTree env) → p = q := by
  induction p with
  | ret position table =>
    intro q h
    cases q with
    | ret position' table' =>
      have entry (env : Assignment _) := Position.result_inj (Reply.Normal.ret.inj (h env))
      exact congrArg₂ Normal.ret (entry (fun _ => false)).1 (funext fun env => (entry env).2)
    | emit | request =>
      have head := h (fun _ => false)
      cases head
  | emit label p ih =>
    intro q h
    cases q with
    | emit label' q =>
      have step (env : Assignment _) := Reply.Normal.emit.inj (h env)
      exact congrArg₂ Normal.emit (step (fun _ => false)).1 (ih q fun env => (step env).2)
    | ret | request =>
      have head := h (fun _ => false)
      cases head
  | request req l r ihl ihr =>
    intro q h
    cases q with
    | request req' l' r' =>
      have step (env : Assignment _) := requestTree_inj (h env)
      have hl : l = l' := ihl l' fun env => by
        have trace := (step env.tail).2.1 (env 0)
        rw [assignment_eta_proof env] at trace
        exact trace
      have hr : r = r' := ihr r' fun env => by
        have trace := (step env.tail).2.2 (env 0)
        rw [assignment_eta_proof env] at trace
        exact trace
      rw [(step (fun _ => false)).1, hl, hr]
    | ret | emit =>
      have head := h (fun _ => false)
      cases head

theorem outcomes_injective_proof (L : List Sorts) :
    Function.Injective (fun p : Normal L 0 => p.outcomes Fin.elim0) := by
  intro p q h
  apply traceTree_inj_proof p q
  intro env
  have empty : env = Fin.elim0 := funext fun i => i.elim0
  rw [empty]
  exact Reply.Normal.outcomesWith_injective _ (Exits.Exit.packed_injective L) h

theorem after_request_proof {L : List Sorts} {n : Nat} (req : Bool) (l r : Normal L (n + 1))
    (env : Assignment n) (right b : Bool) :
    afterPayload req right b ((Normal.request req l r).outcomes env) =
      (if right then r else l).outcomes (env.push b) := by
  cases right <;> exact afterRequest Exits.Exit.packed req
    (fun bit => l.traceTree (env.push bit)) (fun bit => r.traceTree (env.push bit)) _ b

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite
