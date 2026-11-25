module

import Silmaril.Logic.Temporal.TLA.General.Institution.Thms

/-! A signature widening that identifies two rigid names and adds a spare flexible flag. -/

namespace Silmaril.Logic.Temporal.TLA.General.Institution.Examples

open CategoryTheory
open Silmaril.Logic.Temporal.TLA (StutterEquiv)

private def Carrier : Unit → Type := fun _ => Bool

private def source : Scope Unit := ⟨fun _ => Bool, fun _ => Unit⟩
private def target : Scope Unit := ⟨fun _ => Bool, fun _ => Bool⟩

private def widen : source ⟶ target :=
  ⟨⟨fun _ _ => true, fun _ _ => true⟩, fun _ x y _ => Subsingleton.elim (α := Unit) x y⟩

private def ambient : Model Carrier target :=
  ⟨fun _ name => name, fun n _ name => bif name then n != 0 else n == 0⟩

private abbrev tla := roomFunctor Carrier

/-- Both rigid names read the target parameter at `true`. The source flag
follows the target's `true` coordinate at every instant. -/
example :
    let M : Model Carrier source := (tla.map widen).mod.obj ambient
    M.rigid () false = true ∧ M.rigid () true = true ∧
      ∀ n, M.behavior n () () = (n != 0) :=
  ⟨rfl, rfl, fun _ => rfl⟩

private def enabled : Formula Carrier source :=
  .state (.enabled fun ρ s t =>
    s () () ≠ ρ () false ∧ t () () = ρ () false ∧ t () () = ρ () true)

/-- An enabled successor sets the projected flag to the shared rigid value. -/
example : (tla.obj target).Sat ambient ((tla.map widen).sen enabled) := by
  apply (satisfaction widen ambient enabled).2
  exact ⟨fun _ _ => true, by change false ≠ true; decide, rfl, rfl⟩

private def follows : Formula Carrier (source.bindFlex ()) :=
  .always (.state (.atom fun _ s => s.last = s () (Context.old ())))

/-- A hidden flag can follow the changing visible flag after translation under
the binder. The spare target flag is outside the observation of the body. -/
example : (tla.obj target).Sat ambient ((tla.map widen).sen (.existsFlex () follows)) := by
  apply (satisfaction widen ambient (.existsFlex () follows)).2
  let M := ambient.reduct widen.val
  apply (Formula.sat_existsFlex follows M.rigid M.behavior).2
  refine ⟨fun n => (M.behavior n).extend (M.behavior n () ()), StutterEquiv.refl _, ?_⟩
  intro n
  rfl

end Silmaril.Logic.Temporal.TLA.General.Institution.Examples
