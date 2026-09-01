import Tablet.F2PairDigraph
import Tablet.OldPairDigraphProperties
import Tablet.TransitiveTournament

-- [TABLET NODE: F2PairDigraphProperties]
theorem F2PairDigraphProperties (s : Nat) (hs : 4 ≤ s) :
    (∀ v, ¬ (F2PairDigraph s).arc v v) ∧
      ¬ Nonempty (TransitiveTournament (F2PairDigraph s) s) ∧
      @Fintype.card (F2PairDigraph s).vertex (F2PairDigraph s).fintype =
        2 ^ (2 * s - 3) - 2 ^ (s - 2) := by
-- BODY
  sorry
