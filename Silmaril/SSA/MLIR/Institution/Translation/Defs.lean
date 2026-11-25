module

public import Silmaril.SSA.MLIR.Institution.Defs

/-! Typed operation interpretations for pure dialects. -/

@[expose] public section

namespace Silmaril.MLIR.Institution

variable {withRegions : Bool} {S T U : Signature withRegions}

/-- An operation image either forwards its full interface to a target operation or expands
a regionless operation into one target term per result, in the mapped operand context. -/
inductive OpImage (T : Signature withRegions) {a : OpArity withRegions} (p : Profile a T.Ty)
  | forward (op : T.Op p)
  | expand (regionless : a.regionArities.count = 0) (block : Block T p.operand p.result)

/-- A sort map and an image for every operation at its mapped profile. -/
structure Interpretation (S T : Signature withRegions) where
  sort : S.Ty → T.Ty
  image : ∀ {a : OpArity withRegions} {p : Profile a S.Ty}, S.Op p → OpImage T (p.map sort)

namespace OpImage

/-- Instantiate an operation image. Forwarded regions keep their own parameter contexts. -/
def instantiate {a : OpArity withRegions} {p : Profile a T.Ty} {n : Nat} {Γ : Fin n → T.Ty}
    (image : OpImage T p) (args : Block T Γ p.operand)
    (bodies : (r : a.Region) → Block T (p.param r) (p.yield r))
    (i : Fin a.results) : Term T Γ (p.result i) :=
  match image with
  | .forward op => .app op args bodies i
  | .expand _ block => (block i).subst args

/-- Interpret an operation image on already evaluated operands and region functions. -/
def denote {a : OpArity withRegions} {p : Profile a T.Ty} (image : OpImage T p) (M : Model T)
    (args : Assignment M.carrier p.operand)
    (bodies : (r : a.Region) → Assignment M.carrier (p.param r) → Assignment M.carrier (p.yield r)) :
    Assignment M.carrier p.result :=
  match image with
  | .forward op => M.op op args bodies
  | .expand _ block => fun i => (block i).denote M args

end OpImage

namespace Interpretation

/-- Translate recursively through operands and isolated bodies before instantiating an image. -/
def term (f : Interpretation S T) {n : Nat} {Γ : Fin n → S.Ty} {s : S.Ty} :
    Term S Γ s → Term T (f.sort ∘ Γ) (f.sort s)
  | .var i => .var i
  | .app op args bodies i =>
    (f.image op).instantiate (fun j => f.term (args j)) (fun r j => f.term (bodies r j)) i

/-- Forward every operation at its original profile. -/
def id (S : Signature withRegions) : Interpretation S S where
  sort s := s
  image op := .forward op

end Interpretation

namespace OpImage

/-- Translate an operation image, including each result of an expansion. -/
def translate
    {a : OpArity withRegions} {p : Profile a T.Ty} (image : OpImage T p)
    (g : Interpretation T U) : OpImage U (p.map g.sort) :=
  match image with
  | .forward target => g.image target
  | .expand regionless block => .expand regionless (fun i => g.term (block i))

end OpImage

namespace Interpretation

/-- Interpret the operation images of the first lowering using the second. -/
def comp (f : Interpretation S T) (g : Interpretation T U) : Interpretation S U where
  sort := g.sort ∘ f.sort
  image op := (f.image op).translate g

/-- Reindex both sides of a universally quantified block equation. -/
def equation (f : Interpretation S T) (e : Equation S) : Equation T where
  inputs := e.inputs
  outputs := e.outputs
  context := f.sort ∘ e.context
  results := f.sort ∘ e.results
  lhs i := f.term (e.lhs i)
  rhs i := f.term (e.rhs i)

/-- The source interpretation induced by a target model. -/
def reduct (f : Interpretation S T) (M : Model T) : Model S where
  carrier := M.carrier ∘ f.sort
  op o := (f.image o).denote M

end Interpretation
end Silmaril.MLIR.Institution
