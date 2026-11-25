module

public import Silmaril.Raw.SSA.Thesis.LambdaIter.Models.SynElgot
public import Silmaril.Raw.SSA.Thesis.LambdaIter.Models.SynUniformity

/-! # The one-variable λiter syntactic category

Objects are the types of the signature. Arrows are one-variable typed terms
quotiented by the equational theory. The category has binary coproducts and
an iteration operation with fixpoint, naturality, codiagonal and uniformity
for arrows with a pure representative.

The `ElgotCategory` result assumes finite coproducts. The proof of uniformity
uses the syntactic pure-arrow predicate. The construction of an initial object
and of a Cartesian value category with a strong Elgot Freyd functor remains open.
-/
