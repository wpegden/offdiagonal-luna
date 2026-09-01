import Tablet.F2PairDigraph

open scoped BigOperators

-- [TABLET NODE: F2RankSequenceBound]
theorem F2RankSequenceBound (p k : Nat) (hp : 1 ≤ p) (hk : 1 ≤ k) :
    Fintype.card
        { z : (Fin k → (Fin p → ZMod 2)) × (Fin k → (Fin p → ZMod 2)) //
          ∀ ⦃i j : Fin k⦄, i.val ≤ j.val →
            (∑ r, z.1 i r * z.2 j r) = 1 } ≤
      ∑ t ∈ Finset.Icc 1 p,
        Nat.choose k t * 2 ^ (p * (t + k) - Nat.choose (t + 1) 2) := by
-- BODY
  sorry
