import Tablet.F2ForwardIndependentBound
import Tablet.F2AsymptoticCorollary
import Tablet.RandomPermutationReduction
import Tablet.SamplingDeletion

-- [TABLET NODE: ThmClose]
theorem ThmClose :
    ∀ (s a : Nat → Nat), Filter.Tendsto s Filter.atTop Filter.atTop →
      (fun n => (a n : ℝ)) =o[Filter.atTop] (fun n => (s n : ℝ)) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop,
        (RamseyNumber (s n) (s n + a n) : ℝ) ≥
          (1 - ε) * ((s n : ℝ) / Real.exp 1) *
            Real.rpow 2 (((s n : ℝ) + (a n : ℝ) - 1) / 2 -
              (a n : ℝ) ^ 2 / (2 * (s n : ℝ))) := by
-- BODY
  sorry
