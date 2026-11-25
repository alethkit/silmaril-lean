module

public import Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Partial.Defs
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.OrderedState.Partial.Consistency

/-! # Separation of ordered nested RVSDG endpoints -/

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Partial

open OrderedRuntime.Structured (Instruction Values Ty)
open Silmaril.Elgot (iter)

universe u v w
variable {V : Type u} {P E : Dialect.{u,v} V PUnit.{u + 1}} {σ : Type (max u w)}
variable {args ins outs : Ports (Ty V)} {sigs : List (Ports (Ty V))}

/-- Finite Elgot observations use a sequence of completed restarts followed
by a stopped body, all with their returned state. -/
theorem mem_theta {value : V → Type (max u w)}
    (body : Tuple (Values value) ins →
      StateT σ _root_.Part (Tuple (Values value) (Theta.BodyResults ins)))
    (input output : Configuration value σ ins) :
    output ∈ (iter (stepWith body) input.1).run input.2 ↔
      Theta.Iterate (fun x again y => tagged again y ∈ (body x.1).run x.2) input output :=
  Proofs.mem_theta body input output

theorem return_excludes_abnormal (m : Model.{u,v,w} P E σ)
    (g : Graph (Instruction P E) args [] sigs outs) (input : Tuple (Values m.value) args) (store : σ)
    {output : Configuration m.value σ outs} (returned : output ∈ observe m g input store)
    (obs : Abnormal E m.value σ) : ¬ abnormal m g input store obs :=
  Proofs.return_excludes_abnormal m g input store returned obs

/-- A blocked diagnostic is unique and excludes productive divergence. -/
theorem abnormal_unique (m : Model.{u,v,w} P E σ)
    (g : Graph (Instruction P E) args [] sigs outs) (input : Tuple (Values m.value) args) (store : σ)
    {a b : Abnormal E m.value σ} (left : abnormal m g input store a) (right : abnormal m g input store b) :
    a = b :=
  Proofs.abnormal_unique m g input store left right

/-- Every input either has a finite return or reaches a block or a
productive divergent run. Combined with uniqueness, these cases are disjoint. -/
theorem endpoint_exists (m : Model.{u,v,w} P E σ)
    (g : Graph (Instruction P E) args [] sigs outs) (input : Tuple (Values m.value) args) (store : σ) :
    (observe m g input store).Dom ∨ ∃ obs, abnormal m g input store obs :=
  Proofs.endpoint_exists m g input store

end Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Partial
