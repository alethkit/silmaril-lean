module

public import Mathlib.Data.Nat.PadicValNat
public import Silmaril.Logic.Inst.Builders.Core.Defs
public import Silmaril.Logic.Institution.Examples.Unsorted

/-!
# Büchi arithmetic and its Presburger reduct

Both institutions use closed first-order formulas with equality, one fixed signature and
the standard model on `ℕ`. The additive language has `0`, `1` and `+`. Büchi arithmetic
adds the unary function `V₂`, the largest power of two dividing a nonzero input, with
`V₂(0) = 0`. The constants are definable in the addition-only presentation as the additive
identity and the least nonzero natural (where `x ≤ y` means `∃ z, x + z = y`).

Source `zapryagaev-2022-buchi-arithmetics` in `references.bib`, §1, p. 1.
-/

@[expose] public section

namespace Silmaril.Logic.Arithmetic.Buchi

open CategoryTheory Silmaril.Inst
open Silmaril.Logic.Institution.Examples

/-- The largest power of two dividing `n` when `n ≠ 0`, with `V₂(0) = 0`. -/
def valuation (n : ℕ) : ℕ :=
  if n = 0 then 0 else 2 ^ padicValNat 2 n

/-- The symbols of the additive language, indexed by arity. -/
inductive AdditiveOp : ℕ → Type where
  | zero : AdditiveOp 0
  | one : AdditiveOp 0
  | add : AdditiveOp 2

/-- The additive symbols together with unary binary-base valuation. -/
inductive BuchiOp : ℕ → Type where
  | additive {n : ℕ} : AdditiveOp n → BuchiOp n
  | valuation : BuchiOp 1

/-- The first-order signature of Presburger arithmetic. -/
def presburgerSignature : UFOL.Signature := ⟨AdditiveOp, fun _ => Empty⟩

/-- The first-order signature of binary Büchi arithmetic. -/
def buchiSignature : UFOL.Signature := ⟨BuchiOp, fun _ => Empty⟩

/-- The inclusion of the additive signature. -/
def additiveInclusion : presburgerSignature ⟶ buchiSignature :=
  ⟨BuchiOp.additive, id⟩

/-- The standard Büchi structure on `ℕ`. -/
def buchiModel : UFOL.Structure buchiSignature where
  carrier := ℕ
  nonempty := ⟨0⟩
  op o args := match o with
    | .additive .zero => 0
    | .additive .one => 1
    | .additive .add => args 0 + args 1
    | .valuation => valuation (args 0)
  rel r := nomatch r

/-- The standard additive structure on `ℕ`, obtained by forgetting `V₂`. -/
def presburgerModel : UFOL.Structure presburgerSignature :=
  (UFOL.Structure.reduct additiveInclusion).obj buchiModel

/-- The presentation with one signature and one designated first-order model. -/
def standardPlain {S : UFOL.Signature} (M : UFOL.Structure S) : Plain (Disc Unit) where
  Sen _ := UFOL.Sentence S
  map _ := id
  map_id _ _ := rfl
  map_comp _ _ _ := rfl
  Mod _ := Unit
  reduct _ := id
  reduct_id _ _ := rfl
  reduct_comp _ _ _ := rfl
  Sat _ φ := UFOL.Sentence.Holds M φ
  sat_map _ _ _ := Iff.rfl

/-- Presburger arithmetic with its standard-model semantics. -/
abbrev presburger : Institution₀ := (standardPlain presburgerModel).toInst

/-- Binary Büchi arithmetic with its standard-model semantics. -/
abbrev buchi : Institution₀ := (standardPlain buchiModel).toInst

/-- Embed additive sentences into Büchi arithmetic and take the additive reduct on models. -/
def presburgerToBuchi : Comorphism presburger buchi :=
  Comorphism.ofPlain (P := standardPlain presburgerModel) (Q := standardPlain buchiModel)
    (𝟭 _) (fun _ => UFOL.Formula.map additiveInclusion) (fun _ _ => ())
    (fun _ _ φ => UFOL.Formula.holds_map additiveInclusion buchiModel φ Fin.elim0)
    (fun _ _ => rfl) (fun _ _ => rfl)

end Silmaril.Logic.Arithmetic.Buchi
