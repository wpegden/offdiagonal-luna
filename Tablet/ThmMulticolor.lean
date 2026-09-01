import Tablet.F2ForwardIndependentBound
import Tablet.MulticolorRamseyNumber
import Tablet.RandomHomomorphismColoring

-- [TABLET NODE: ThmMulticolor]
theorem ThmMulticolor :
    ∀ ell : Nat, 3 ≤ ell → ∃ c : ℝ, 0 < c ∧ ∃ S : Nat,
      ∀ s : Nat, S ≤ s →
        (MulticolorRamseyNumber s ell : ℝ) ≥
          c * Real.rpow 2 (((ell - 1 : Nat) : ℝ) * (s : ℝ) / 2) := by
-- BODY
  sorry
