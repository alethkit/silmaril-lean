module

public import Silmaril.Semantics.Calco2019.Trace.Vanishing.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.Vanishing

/-! # Vanishing for two jointly guarded feedback states -/

public section

universe u v

namespace Silmaril.Calco2019.Guardedness.TwoStateBody

open CategoryTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}
  {A B U V : K} (D : TwoStateBody G A B U V) (F : G.Conway)

theorem second_guard : G.guarded D.second := Proofs.Feedback.second_guard D

theorem afterSecond_guard :
    G.guarded (D.first ≫ P.desc (𝟙 _) (F.iterate D.second D.second_guard)) :=
  Proofs.Feedback.afterSecond_guard F D

/-- Simultaneous feedback over both states equals feedback over the second
state followed by feedback over the first. The common guard is on their sum. -/
theorem feedback_vanish_pair :
    let g := P.desc D.first D.second
    let v := F.iterate D.second D.second_guard
    let q := D.first ≫ P.desc (𝟙 _) v
    let u := F.iterate q (D.afterSecond_guard F)
    D.entry ≫ P.assoc ≫ P.desc (𝟙 B) (F.iterate (g ≫ P.assoc) D.guarded) =
      D.entry ≫ P.desc (𝟙 _) v ≫ P.desc (𝟙 B) u :=
  Proofs.Feedback.feedback_vanish_pair F D

end Silmaril.Calco2019.Guardedness.TwoStateBody
