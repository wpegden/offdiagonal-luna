import Tablet.OldPairDigraph
import Tablet.OldPairDigraphProperties
import Tablet.OldPolarityParameters
import Tablet.OldCoherentTreeCount
import Tablet.AlonRodlBound

-- [TABLET NODE: OldPolarityConstruction]
theorem OldPolarityConstruction (delta : ℝ) (hdelta : 0 < delta) :
    ∃ L : Nat, 0 < L ∧ ∀ s k : Nat, L ≤ s → L * s ≤ k →
      ∃ q : Nat, (∃ m : Nat, q = 2 ^ m) ∧
        (q : ℝ) ≤ delta / 200 * ((k : ℝ) / (s : ℝ)) /
            Real.log ((k : ℝ) / (s : ℝ)) ∧
        delta / 200 * ((k : ℝ) / (s : ℝ)) /
            Real.log ((k : ℝ) / (s : ℝ)) ≤ 2 * q ∧
        ∃ G : LoopGraph,
          (∀ (a b : Fin s → G.vertex),
            (∀ i, ¬ G.adj (a i) (b i)) →
            (∀ ⦃i j : Fin s⦄, i.val < j.val → G.adj (a i) (b j)) → False) ∧
          ¬ Nonempty (TransitiveTournament (OldPairDigraph G) s) ∧
          ((q : ℝ) ^ (2 * (s - 2)) / 2 ≤
            (@Fintype.card (OldPairDigraph G).vertex
              (OldPairDigraph G).fintype : ℝ)) ∧
          (ForwardIndependentCount (OldPairDigraph G) k : ℝ) ≤
            (32 * Real.rpow (q : ℝ)
              (2 * (s - 2 : Nat) - ((s - 3 : Nat) : ℝ) *
                (1 - delta / 5))) ^ k := by
-- BODY
  sorry
