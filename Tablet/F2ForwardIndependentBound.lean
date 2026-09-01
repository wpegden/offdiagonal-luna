import Tablet.F2PairDigraphProperties
import Tablet.F2RankSequenceBound
import Tablet.ForwardIndependentCount

open scoped BigOperators

-- [TABLET NODE: F2ForwardIndependentBound]
theorem F2ForwardIndependentBound (s k : Nat) (hs : 4 ≤ s) (hsk : s ≤ k) :
    ∃ D : LooplessDigraph,
      D = F2PairDigraph s ∧
      ¬ Nonempty (TransitiveTournament D s) ∧
      @Fintype.card D.vertex D.fintype =
        2 ^ (2 * s - 3) - 2 ^ (s - 1) - 2 ^ (s - 2) + 1 ∧
      (ForwardIndependentCount D k : ℝ) ≤
        (∑ t ∈ Finset.Icc 1 (s - 1),
          (Nat.choose k t *
            2 ^ ((s - 1) * (t + k) - Nat.choose (t + 1) 2) : Nat) : ℝ) := by
-- BODY
  sorry
