import Tablet.ForwardIndependentCount
import Tablet.AlonRodlBound
import Tablet.RootedTreeCounting
import Tablet.TransitiveTournament

-- [TABLET NODE: DStarCounting]
theorem DStarCounting (t : Nat) (ht : 2 ≤ t) :
    ∃ C : Nat, 0 < C ∧
      ∀ q : Nat, C ≤ q → (∃ m : Nat, q = 2 ^ m) →
        ∀ k : Nat, C * q * (Nat.log q) ^ 2 ≤ k →
          ∃ D : LooplessDigraph,
            ¬ Nonempty (TransitiveTournament D (t + 1)) ∧
            2 ^ (2 * t - 1) / 4 ≤
              @Fintype.card D.vertex D.fintype ∧
            (ForwardIndependentCount D k : ℝ) ≤
              (C * q ^ t : ℝ) ^ k := by
-- BODY
  sorry
