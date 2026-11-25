module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Defs

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}

/-- Compare a call entry at the same argument and result ports. -/
inductive Activation.Related (m : Machine.{u, v, w} Op) (ids : GlobalRel)
    {outs : Ports (Ty V S)} : Activation m outs → Activation m outs → Prop where
  | intro {args : Ports (Ty V S)} {left right : m.Val (.value (.function args outs))}
      {inputL inputR : Tuple m.Val args}
      (callee : ValueRelated m ids left right) (inputs : TupleRelated m ids inputL inputR) :
      Activation.Related m ids ⟨args, left, inputL⟩ ⟨args, right, inputR⟩

/-- Inspecting corresponding activations preserves return, call and unsupported outcomes. -/
inductive Outcome.Related (m : Machine.{u, v, w} Op) (ids : GlobalRel) :
    {outs outs' : Ports (Ty V S)} → Outcome m outs → Outcome m outs' → Prop where
  | returned {outs outs' : Ports (Ty V S)} {left : Tuple m.Val outs} {right : Tuple m.Val outs'}
      (paired : TupleRelated m ids left right) :
      Outcome.Related m ids (.returned left) (.returned right)
  | enter {outs : Ports (Ty V S)} {left right : Activation m outs}
      (paired : Activation.Related m ids left right) :
      Outcome.Related m ids (.enter left) (.enter right)
  | unsupported {outs outs' : Ports (Ty V S)} :
      Outcome.Related m ids (.unsupported (outs := outs)) (.unsupported (outs := outs'))

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail
