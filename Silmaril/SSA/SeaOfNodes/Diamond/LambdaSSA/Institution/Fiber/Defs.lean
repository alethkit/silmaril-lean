module

public import Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Institution.Thms
public import Silmaril.SSA.Isotope.Institution.Observational.Thms

/-! A fixed instruction alphabet of the existing λSSA observational
institution for each native diamond signature. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Institution.Fiber

open CategoryTheory
open RVSDG (Tuple)
open Isotope.Institution.Observational (lambdaSSA)
open Isotope.Morphism.SSAIter (ScopedRegion)

universe u v w x
variable {Data : Type u} {P : Diamond.Institution.Signature.{u, v} Data}
variable {inputs : List (ValueSort Data)} {out : ValueSort Data}

-- The institutional universe bounds combine the value and state levels.
-- The underlying observational model still has separate carriers at those levels.
set_option linter.checkUnivs false in
/-- One existing λSSA observational institution, with a fixed alphabet and one exit. -/
abbrev fixedFiber (P : Diamond.Institution.Signature.{u, v} Data) :=
  (lambdaSSA.{max u v, max u w, x} (Primitive P.op) 1).inst

set_option linter.checkUnivs false in
/-- The existing room at the given ambient value scope. -/
abbrev fiberRoom (P : Diamond.Institution.Signature.{u, v} Data) (n : Nat) :=
  (fixedFiber.{u, v, w, x} P).I.obj (Discrete.mk n)

/-- Keep the emitted CFG and forget the types after obtaining its scope proof. -/
def scope (r : GeneratedRegion P inputs out) : ScopedRegion (Primitive P.op) 1 inputs.length :=
  ⟨r.val, by
    simpa only [initialContext, dataPorts, List.length_map, List.length_singleton] using
      r.hasType.scoped⟩

/-- Use the actual equation constructor of the existing observational room. -/
def translateEquation (e : Equation P) :
    Silmaril.Logic.Institution.Observational.Sentence (ScopedRegion (Primitive P.op) 1 e.inputs.length) :=
  .eq (scope e.lhs) (scope e.rhs)

/-- One existing observational model for each typed input. The bound
environment is the restriction of the lowering's encoding to the input
scope. The primitive relation leaves ambient state unchanged. -/
def inputModel (m : Model.{u, v, w} P.op) (σ : Type x)
    (input : Tuple (Val m.value) (dataPorts inputs)) :
    Isotope.Institution.Observational.Model.{max u v, max u w, x} (Primitive P.op) inputs.length where
  α := Atom m
  σ := σ
  instr := instruction m
  faults _ _ _ _ := False
  prim _ _ _ := False
  bound i := inputEnv m input i.val

end Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Institution.Fiber
