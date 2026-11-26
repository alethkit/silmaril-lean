module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Typing.Thms

/-! # Checked removal of redundant unit binders at packed routers -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {X : Syntax.Ty}
variable {Γ R L : List Syntax.Ty}

/-- Insert a literal unit binder with exact weakening of every old variable. -/
def bindUnusedUnit (r : Typed Φ Γ L) : Typed Φ Γ L :=
  ⟨.let₁ .unit (r.val.renameVars Nat.succ),
    .let₁ .unit (r.property.renameVars (LambdaSSA.Ren.wk Γ (.unit : Syntax.Ty)))⟩

/-- Re-emit a proposed readback with optional redundant binders at the packed
routers. Entry and producer syntax are the same as in the exact readback. -/
def Readback.withRouterUnits (w : Readback Φ X R L) (units : Fin R.length → Bool) : Typed Φ [X] L :=
  let blocks (i : Fin R.length) : Typed Φ (R.get i :: [X]) (R ++ L) :=
    if units i then bind (w.producer i).typed (bindUnusedUnit (route R L))
    else w.routed i
  ⟨nativeFeedback w.entry blocks, nativeFeedback_hasType w.entry blocks⟩

/-- Detect the possible binder only at the continuation of the packed
producer. The subsequent exact comparison validates its body. -/
def hasRouterUnit (r : LambdaSSA.Region Φ) (i : Nat) : Bool :=
  match r with
  | .cfg _ n blocks =>
    if bound : i < n then
      match blocks ⟨i, bound⟩ with
      | .cfg _ 1 next =>
        match next 0 with
        | .let₁ .unit _ => true
        | _ => false
      | _ => false
    else false
  | _ => false

variable [DecidableEq Φ]

/-- The re-emitted entry, producers, and possibly padded routers must match
the original syntax exactly. Only the matched padding is removed. -/
def normalizeRouterUnits (R : List Syntax.Ty) (raw : Typed Φ [X] L) : Option (Typed Φ [X] L) := do
  let w ← propose R L raw.val
  let units := fun i : Fin R.length => hasRouterUnit raw.val i
  if sameRegion raw.val (w.withRouterUnits units).val then some w.typed else none

/-- Run the existing exact recognizer on the checked normal form. -/
def recognizeRouterUnits (R : List Syntax.Ty) (raw : Typed Φ [X] L) : Option (Readback Φ X R L) :=
  (normalizeRouterUnits R raw).bind (recognize R)

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native
