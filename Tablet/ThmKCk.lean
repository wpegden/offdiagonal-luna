import Tablet.F2ForwardIndependentBound
import Tablet.RandomPermutationReduction
import Tablet.SamplingDeletion

-- [TABLET NODE: ThmKCk]
theorem ThmKCk :
    ∀ C : ℝ, 1 < C → ∃ S : Nat, ∀ s : Nat, S ≤ s →
      (RamseyNumber s (Nat.ceil (C * (s : ℝ))) : ℝ) ≥
        Real.rpow 2 ((1 - 1 / (2 * C)) * (s : ℝ)) := by
-- BODY
  sorry
