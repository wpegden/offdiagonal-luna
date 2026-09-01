import Tablet.F2RankSequenceBound

open scoped BigOperators

-- [TABLET NODE: F2AsymptoticCorollary]
theorem F2AsymptoticCorollary :
    ∀ (s a : Nat → Nat), Filter.Tendsto s Filter.atTop Filter.atTop →
      (fun n => (a n : ℝ)) =o[Filter.atTop] (fun n => (s n : ℝ)) →
      ∃ e : Nat → ℝ,
        (fun n => e n) =o[Filter.atTop] (fun n => (s n : ℝ)) ∧
        ∀ᶠ n in Filter.atTop,
          (∑ t ∈ Finset.Icc 1 (s n - 1),
            (Nat.choose (s n + a n) t *
              2 ^ ((s n - 1) * (t + (s n + a n)) -
                Nat.choose (t + 1) 2) : Nat) : ℝ) ≤
            Real.rpow 2
              (3 / 2 * (s n : ℝ) ^ 2 +
                (a n : ℝ) * (s n : ℝ) - 5 / 2 * (s n : ℝ) + e n) := by
-- BODY
  sorry
