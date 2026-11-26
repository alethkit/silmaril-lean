module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Capture.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.WellFormed.Thms

/-! # Checked admission and capture closure for normalized φ graphs -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified

open Silmaril.SSA.LambdaRTL
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics (Env)
open LetCase.LocallyNameless (Tm HasType)

universe u v w
variable {V K Base : Type u} {F : Type v} {n : Nat} [DecidableEq V] [DecidableEq K]

/-- The actual named lexical table fixes the positional internal interface. -/
abbrev blockCount (source : CFG.Cyclic.Phi.Graph V K F) : Nat :=
  (CFG.Cyclic.Versioning.compile (CFG.Cyclic.Phi.lower source)).blocks.length

variable [HasTy F (Ty Base)]

/-- Global source SSA and exact typing of the accepted open target are distinct
evidence. The target must elaborate from the actual φ lowering. -/
structure Admission (source : CFG.Cyclic.Phi.Graph V K F) (inputs : List V)
    (captures : Fin n → Option V) (β : BoundCtx (Ty Base) n)
    (R : Fin (blockCount source) → Ty Base) (L : Fin 1 → Ty Base) where
  wellFormed : CFG.Cyclic.Phi.GlobalSSA.WellFormed source inputs
  graph : FiniteCFG F (blockCount source) 1 n
  elaborated : NamedFlat.compile (CFG.Cyclic.Phi.lower source) [none] captures = some graph
  typed : graph.HasType β R L

/-- Check global SSA at the source, then elaborate and check the supplied
Isotope typing profile. Each check can reject independently. -/
def admit [DecidableEq Base] (source : CFG.Cyclic.Phi.Graph V K F) (inputs : List V)
    (certificate : CFG.Cyclic.Phi.GlobalSSA.Certificate V K) (captures : Fin n → Option V)
    (β : BoundCtx (Ty Base) n) (R : Fin (blockCount source) → Ty Base) (L : Fin 1 → Ty Base) :
    Option (Admission source inputs captures β R L) :=
  if accepted : CFG.Cyclic.Phi.GlobalSSA.check source inputs certificate = true then
    (NamedFlat.compileTyped (CFG.Cyclic.Phi.lower source) [none] captures β R L).map fun result =>
      ⟨CFG.Cyclic.Phi.GlobalSSA.check_sound accepted, result.val, result.property.1, result.property.2⟩
  else none

variable {source : CFG.Cyclic.Phi.Graph V K F} {inputs : List V} {captures : Fin n → Option V}
  {β : BoundCtx (Ty Base) n} {R : Fin (blockCount source) → Ty Base} {L : Fin 1 → Ty Base}

/-- A closed target for one admitted graph and one specific capture expression. -/
structure Closed (admitted : Admission source inputs captures β R L) (input : Tm Empty F 0) where
  graph : FiniteCFG F (blockCount source) 1 0
  typed : graph.HasType .nil R L
  closes : Capture.Closes β input admitted.graph graph

/-- Run the existing typed closure checker. The result carries its own typing
and the erasure equation relating it to the admitted open graph. -/
def Admission.close [DecidableEq Base] (admitted : Admission source inputs captures β R L)
    (input : Tm Empty F 0) (typed : HasType F .nil .nil input (Region.packedInputType β.toList)) :
    Option (Closed admitted input) :=
  (Capture.close β R L admitted.graph admitted.typed input typed).map fun result =>
    ⟨result.val, result.property.1, result.property.2⟩

/-- The positional environment is determined by the version-zero captures of
the source store. The private packet name and unused positions carry unit. -/
def captureEnv {W α : Type w} (captures : Fin n → Option W) (store : W → Value α) : Env α :=
  fun i => if inside : i < n then (captures ⟨i, inside⟩).elim .unit store else .unit

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified
