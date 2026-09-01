import Tablet.CompleteColoring
import Tablet.ForwardIndependentCount
import Tablet.MonochromaticClique
import Tablet.TransitiveTournament

-- [TABLET NODE: RandomHomomorphismColoring]
theorem RandomHomomorphismColoring
    (D : LooplessDigraph) (s ell n : Nat)
    (hfree : ¬ Nonempty (TransitiveTournament D s))
    (hprob : (Nat.choose n s : ℝ) *
        ((ForwardIndependentCount D s : ℝ) /
          (@Fintype.card D.vertex D.fintype : ℝ) ^ s) ^ (ell - 1) < 1) :
    ∃ c : CompleteColoring n ell,
      ¬ Nonempty (MonochromaticClique c s) := by
-- BODY
  sorry
