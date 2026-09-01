import Tablet.OldPolarityConstruction
import Tablet.RandomPermutationReduction
import Tablet.SamplingDeletion

-- [TABLET NODE: ThmOffDiagonalGeneral]
theorem ThmOffDiagonalGeneral :
    ∀ delta : ℝ, 0 < delta → ∃ L : Nat, 0 < L ∧
      ∀ s k : Nat, L ≤ s → L * s ≤ k →
        (RamseyNumber s k : ℝ) ≥
          Real.rpow ((k : ℝ) / (s : ℝ)) ((1 - delta) * (s : ℝ)) := by
-- BODY
  sorry
