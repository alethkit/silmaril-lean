module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Direct.Defs
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Equality.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Link
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Correct

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Direct.Proofs

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op}
variable {table : MemberSummaries V S} {imports : Ports (Ty V S)} {scope : Scope m}
variable {fn : Function V S}

private theorem capture_get {Ty : Type u} {F : Ty → Type w} {context params : Ports Ty} {ty : Ty}
    (p : Port (context ++ params) ty) (q : Port context ty)
    (selected : capturePort context p = some q) (captured : Tuple F context) (args : Tuple F params) :
    (prependContext args captured).get p = captured.get q := by
  induction captured with
  | nil => simp [capturePort] at selected
  | cons _ tail ih =>
    cases p with
    | head =>
      cases selected
      rfl
    | tail p =>
      cases found : capturePort _ p with
      | none => simp [capturePort, found] at selected
      | some actual =>
        have eq : Port.tail actual = q := by simpa only [capturePort, found, Option.map_some, Option.some.injEq] using selected
        subst q
        exact ih p actual found

private theorem read_get {Ty : Type u} {F : Ty → Type w} {args users : Ports Ty}
    {past : List (Ports Ty)} {ty : Ty}
    (wires : Wires args past users) (p : Port users ty)
    (inputs : Tuple F args) (locals : Locals F past) :
    (wires.read inputs locals).get p = (Wires.read (.cons (wires.get p) .nil) inputs locals).get .head := by
  induction p with
  | head => cases wires; rfl
  | tail _ ih => cases wires; exact ih _

theorem project_read {Ty : Type u} {F : Ty → Type w} {imports context params users : Ports Ty}
    {past localSigs : List (Ports Ty)} (wires : Wires imports past context)
    (requested : Wires (context ++ params) localSigs users) (sources : Wires imports past users)
    (found : project wires requested = some sources)
    (inputs : Tuple F imports) (locals : Locals F past) (args : Tuple F params) (inner : Locals F localSigs) :
    sources.read inputs locals = requested.read (prependContext args (wires.read inputs locals)) inner := by
  induction requested with
  | nil => cases found; rfl
  | cons origin rest ih =>
    cases origin with
    | output => simp [project] at found
    | arg p =>
      cases selected : capturePort _ p with
      | none => simp [project, selected] at found
      | some q =>
        cases more : project wires rest with
        | none => simp [project, selected, more] at found
        | some tail =>
          have same : Tuple.cons (wires.get q) tail = sources := by
            simpa [project, selected, more] using found
          subst sources
          exact congrArg₂ Tuple.cons ((read_get wires q inputs locals).symm.trans
            (capture_get p q selected (wires.read inputs locals) args).symm) (ih tail more)

theorem widen_read {args users head : Ports (Ty V S)} {past : List (Ports (Ty V S))}
    (wires : Wires args past users) (inputs : Tuple m.Val args) (locals : Locals m.Val past)
    (value : Tuple m.Val head) :
    (widen wires).read inputs (locals.snoc value) = wires.read inputs locals := by
  induction wires with
  | nil => rfl
  | cons origin _ ih =>
    exact congrArg₂ Tuple.cons
      (Isomorphism.Local.Gamma.extendOrigin_read origin inputs locals value) ih

private theorem drop_read {args tail : Ports (Ty V S)} {past : List (Ports (Ty V S))}
    (front : Ports (Ty V S)) (wires : Wires args past (front ++ tail))
    (inputs : Tuple m.Val args) (locals : Locals m.Val past) :
    Wires.read (StaticDemand.Family.dropPrefix front wires) inputs locals =
      StaticDemand.Family.dropPrefix front (wires.read inputs locals) := by
  induction front with
  | nil => rfl
  | cons _ rest ih =>
    cases wires with
    | cons _ rest => exact ih rest

theorem seed_selects (family : StaticDemand.Family Op table imports) (i : Fin table.members.length)
    (inputs : Tuple m.Val imports) (origins : Wires imports [memberPorts table.members] (table.at i).captures)
    (found : phiCaptures family i = some origins) :
    let seeded := Scope.seed family inputs inputs
    selects seeded.guardL i ((seedWires i origins).read inputs seeded.localsL) := by
  let captured := family.captures.read inputs PUnit.unit
  let refs := family.references captured
  have written := project_read (widen family.captures)
    (StaticDemand.Family.dropPrefix (memberPorts table.members) (family.memberWires i))
    origins found inputs (past := [memberPorts table.members]) (refs, PUnit.unit)
    refs (memberPrefix table.members i.val (family.memberValue captured))
  have outer : (widen (head := memberPorts table.members) family.captures).read inputs (refs, PUnit.unit) = captured :=
    widen_read family.captures inputs PUnit.unit refs
  rw [outer] at written
  refine ⟨StaticDemand.Proofs.member_get table.members (family.memberValue captured) i, ?_⟩
  exact written.trans (drop_read (memberPorts table.members) (family.memberWires i)
    (prependContext refs captured) (memberPrefix table.members i.val (family.memberValue captured)))

theorem new_selects (binding : Binding Op scope.table imports scope.past fn)
    (inputs : Tuple m.Val imports) (locals : Locals m.Val scope.past) (guard : Guard m scope.table) :
    selects (binding.extendGuard guard inputs locals) (0 : Fin (scope.table.members.length + 1))
      ((newWires binding).read inputs (locals.snoc (.cons (binding.value inputs locals) .nil))) := by
  exact ⟨congrArg (fun xs : Tuple m.Val [fn.port] => xs.get .head)
    (Prefix.Proofs.last_read inputs locals (binding.value inputs locals)),
    widen_read binding.captures inputs locals (.cons (binding.value inputs locals) .nil)⟩

theorem projected_call {context params : Ports (Ty V S)} (captures : Wires imports scope.past context)
    (i : Fin scope.table.members.length)
    (target : Port (context ++ params) (scope.table.at i).fn.port)
    (witnesses : Wires (context ++ params) [] (scope.table.at i).captures)
    (sources expected : Wires imports scope.past (CallPorts scope.table i))
    (found : project captures (.cons (.arg target) witnesses) = some sources)
    (same : sources.addresses = expected.addresses)
    (inputs : Tuple m.Val imports) (locals : Locals m.Val scope.past) (guard : Guard m scope.table)
    (resolved : selects guard i (expected.read inputs locals)) (args : Tuple m.Val params) :
    let entry := prependContext args (captures.read inputs locals)
    guard i (entry.get target) (witnesses.read entry PUnit.unit) := by
  have h := project_read captures _ sources found inputs locals args PUnit.unit
  have eq := NestedTheta.Equality.addresses_injective sources expected same
  rw [eq] at h
  unfold selects at resolved
  rw [h] at resolved
  exact resolved

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Direct.Proofs
