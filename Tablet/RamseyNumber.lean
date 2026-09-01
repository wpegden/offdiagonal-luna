import Tablet.Preamble
import Tablet.LoopGraph
import Tablet.CliqueWitness
import Tablet.IndependentWitness

-- [TABLET NODE: RamseyNumber]
noncomputable def RamseyNumber (s k : Nat) : Nat :=
-- BODY
  sInf { n : Nat | ∀ (G : LoopGraph),
    @Fintype.card G.vertex G.fintype = n →
      (∀ v, ¬ G.adj v v) →
      Nonempty (CliqueWitness G s) ∨ Nonempty (IndependentWitness G k) }
