import Tablet.Preamble
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

-- [TABLET NODE: StrictSpanGrowth]
theorem StrictSpanGrowth
    (K V : Type) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W : Submodule K V) (v : V)
    (hv : v ∉ W) :
    Module.finrank K (↑(W ⊔ Submodule.span K ({v} : Set V)) : Type) =
      Module.finrank K W + 1 := by
-- BODY
  exact Submodule.finrank_sup_span_singleton hv
