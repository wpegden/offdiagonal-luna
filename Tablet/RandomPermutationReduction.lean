import Tablet.CliqueWitness
import Tablet.ForwardIndependentCount
import Tablet.IndependentSetCount
import Tablet.TransitiveTournament

-- [TABLET NODE: RandomPermutationReduction]
theorem RandomPermutationReduction
    (D : LooplessDigraph) (s k : Nat)
    (hfree : ¬ Nonempty (TransitiveTournament D s)) (hk : 1 ≤ k) :
    ∃ G : LoopGraph,
      @Fintype.card G.vertex G.fintype = @Fintype.card D.vertex D.fintype ∧
      (∀ v, ¬ G.adj v v) ∧
      ¬ Nonempty (CliqueWitness G s) ∧
      (IndependentSetCount G k : ℝ) ≤
        (Real.exp 1 / (k : ℝ)) ^ k *
          (ForwardIndependentCount D k : ℝ) := by
-- BODY
  sorry
