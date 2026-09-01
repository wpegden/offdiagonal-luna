import Tablet.ForwardIndependentCount
import Tablet.AlonRodlBound
import Tablet.RootedTreeCounting
import Tablet.TransitiveTournament

-- [TABLET NODE: OldPolarityConstruction]
theorem OldPolarityConstruction (delta : ℝ) (hdelta : 0 < delta) :
    ∃ L : Nat, 0 < L ∧ ∀ s k : Nat, L ≤ s → L * s ≤ k →
      ∃ q : Nat, (∃ m : Nat, q = 2 ^ m) ∧
        (q : ℝ) ≤ delta / 200 * ((k : ℝ) / (s : ℝ)) /
            Real.log ((k : ℝ) / (s : ℝ)) ∧
        delta / 200 * ((k : ℝ) / (s : ℝ)) /
            Real.log ((k : ℝ) / (s : ℝ)) ≤ 2 * q ∧
        ∃ D : LooplessDigraph,
          ¬ Nonempty (TransitiveTournament D s) ∧
          ((q : ℝ) ^ (2 * (s - 2)) / 2 ≤
            (@Fintype.card D.vertex D.fintype : ℝ)) ∧
          (ForwardIndependentCount D k : ℝ) ≤
            (32 * Real.rpow (q : ℝ)
              (2 * (s - 2 : Nat) - ((s - 3 : Nat) : ℝ) *
                (1 - delta / 5))) ^ k := by
-- BODY
  sorry
