module

import Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Institution.Restricted.Thms

namespace Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Institution.Restricted

open CategoryTheory

private abbrev sig : Diamond.Institution.Signature.{0, 0} Empty :=
  ⟨fun _ _ => Empty⟩

private def native : Diamond.Model.{0, 0, 0} sig.op where
  value sort := sort.elim
  run op _ := op.elim

private theorem native_unique (M : Diamond.Model.{0, 0, 0} sig.op) : M = native := by
  cases M with
  | mk value run =>
    have equal : value = native.value := funext fun sort => sort.elim
    cases equal
    congr 1
    funext _ _ op
    exact op.elim

private abbrev induced := Diamond.MLIR.model native

private def reverseSelector (n : Nat) : ULift.{0} (Fin n) ≃ ULift.{0} (Fin n) where
  toFun x := ⟨x.down.rev⟩
  invFun x := ⟨x.down.rev⟩
  left_inv := fun ⟨i⟩ => congrArg ULift.up (Fin.rev_rev i)
  right_inv := fun ⟨i⟩ => congrArg ULift.up (Fin.rev_rev i)

private def encode : (t : Diamond.Ty Empty) → induced.carrier t ≃ induced.carrier t
  | .control n => reverseSelector n
  | _ => Equiv.refl _

private def recoded : Presentation sig where
  base := transport induced encode
  predicate := Equiv.refl _
  selector := reverseSelector

private theorem recoded_normal : recoded.normalize = induced := by
  have decode_eq : recoded.decode = fun t => (encode t).symm := by
    funext t
    cases t with
    | value sort => cases sort <;> rfl
    | control => rfl
    | state sort => cases sort
  exact (congrArg (fun decode => transport recoded.base decode) decode_eq).trans
    (transport_inverse induced encode)

private theorem op_heq {M N : Silmaril.MLIR.Institution.Model (target sig)} (h : M = N)
    {a : Silmaril.MLIR.Institution.OpArity true}
    {p : Silmaril.MLIR.Institution.Profile a (target sig).Ty} (op : (target sig).Op p) :
    HEq (M.op op) (N.op op) := by
  cases h
  rfl

private def admitted : Model sig where
  toPresentation := recoded
  dispatch out :=
    eq_of_heq (op_heq (recoded_normal.trans (congrArg Diamond.MLIR.model (native_unique recoded.extract).symm))
      (.simple (.dispatch out)))
  gamma entry exit extra :=
    eq_of_heq (op_heq (recoded_normal.trans (congrArg Diamond.MLIR.model (native_unique recoded.extract).symm))
      (.gamma entry exit extra))

private abbrev predicatePort : Diamond.Ty Empty := .value .predicate

private abbrev selection : RVSDG.MLIR.Graph.Op (source sig.op)
    (RVSDG.MLIR.Graph.profile [.control 2] [predicatePort] 2 [] [predicatePort]) :=
  .gamma [] [predicatePort] 0

private def selectorInput (i : Fin 2) :
    induced.carrier (.control 2) := ULift.up i

private def branches (branch : Fin 2)
    (_ : Silmaril.MLIR.Institution.Assignment induced.carrier ([].get (α := Diamond.Ty Empty))) :
    Silmaril.MLIR.Institution.Assignment induced.carrier [predicatePort].get :=
  fun i => Fin.cases (ULift.up (branch.val == 1)) (fun j => j.elim0) i

-- At the raw selector 1, the recoded model selects arm 0. Canonical induced models select arm 1.
example : admitted.base.op selection (fun i => Fin.cases (selectorInput 1) (fun j => j.elim0) i)
    branches (0 : Fin 1) = ULift.up false := rfl

example (M : Diamond.Model.{0, 0, 0} sig.op) : admitted.base ≠ Diamond.MLIR.model M := by
  intro equal
  have same := eq_of_heq (op_heq (equal.trans (congrArg Diamond.MLIR.model (native_unique M))) selection)
  have result := congrFun (congrFun (congrFun same
    (fun i => Fin.cases (selectorInput 1) (fun j => j.elim0) i)) branches) (0 : Fin 1)
  change (ULift.up false : ULift Bool) = ULift.up true at result
  cases result

-- #3266's bad gamma keeps the canonical carriers and simple operations but ignores the selector.
private def firstArm : Silmaril.MLIR.Institution.Model (target sig) where
  carrier := induced.carrier
  op
    | .simple op, args, regions => induced.op (.simple op) args regions
    | .gamma _ _ _, args, regions => regions ⟨0, Nat.zero_lt_succ _⟩ (fun i => args i.succ)

example : ¬ ∃ M : Model sig, M.base = firstArm := by
  rintro ⟨M, equal⟩
  cases M with
  | mk presentation _ gamma =>
    cases presentation with
    | mk raw predicate selector =>
      change raw = firstArm at equal
      subst raw
      have result := congrFun (congrFun (congrFun (gamma [] [predicatePort] 0)
        (fun i => Fin.cases (selectorInput 1) (fun j => j.elim0) i)) branches) (0 : Fin 1)
      change predicate (predicate.symm (ULift.up false)) = ULift.up true at result
      have impossible := (predicate.apply_symm_apply (ULift.up false)).symm.trans result
      cases impossible

-- The singleton carrier from #3266 cannot supply a Boolean decoding.
example : ¬ Nonempty (Unit ≃ ULift.{0} Bool) := by
  rintro ⟨decode⟩
  have equal : ULift.up false = ULift.up true := calc
    ULift.up false = decode (decode.symm (ULift.up false)) := (decode.apply_symm_apply _).symm
    _ = decode (decode.symm (ULift.up true)) := congrArg decode (Subsingleton.elim _ _)
    _ = ULift.up true := decode.apply_symm_apply _
  cases equal

end Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Institution.Restricted
