import Tablet.DStarCounting
import Tablet.FiniteRamseyPositivity
import Tablet.RandomPermutationReduction
import Tablet.SamplingDeletion

-- [TABLET NODE: ThmMain]
theorem ThmMain :
    ∀ s : Nat, 3 ≤ s → ∃ c : ℝ, 0 < c ∧
      ∀ k : Nat, 2 ≤ k →
        (RamseyNumber s k : ℝ) ≥
          c * (k : ℝ) ^ (s - 1) /
            (Real.log (k : ℝ)) ^ (2 * s - 4) := by
-- BODY
  sorry
