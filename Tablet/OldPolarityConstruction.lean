import Tablet.OldPairDigraph
import Tablet.OldPairDigraphProperties
import Tablet.OldPolarityParameters
import Tablet.OldCoherentTreeCount
import Tablet.AlonRodlBound
import Tablet.ExpanderMixing
import Tablet.ForwardIndependentTuple
import Tablet.ForwardIndependentCount

-- [TABLET NODE: OldPolarityConstruction]
theorem OldPolarityConstruction (delta : ℝ) (hdelta : 0 < delta) :
    ∃ L : Nat, 0 < L ∧ ∀ s k : Nat, L ≤ s → L * s ≤ k →
      ∃ q : Nat, (∃ m : Nat, q = 2 ^ m) ∧ IsPrimePow q ∧ 16 ≤ q ∧
        (q : ℝ) ≤ delta / 200 * ((k : ℝ) / (s : ℝ)) /
            Real.log ((k : ℝ) / (s : ℝ)) ∧
        delta / 200 * ((k : ℝ) / (s : ℝ)) /
            Real.log ((k : ℝ) / (s : ℝ)) ≤ 2 * q ∧
        ∃ K : Type, ∃ hfield : Field K, ∃ hfintype : Fintype K,
          @Fintype.card K hfintype = q ∧
          ∃ ht : 2 ≤ s - 2,
            let G := @PolarityGraph K hfield hfintype (s - 2) ht
            let D := OldPairDigraph G
            (∀ (a b : Fin s → G.vertex),
              (∀ i, ¬ G.adj (a i) (b i)) →
              (∀ ⦃i j : Fin s⦄, i.val < j.val → G.adj (a i) (b j)) → False) ∧
            ¬ Nonempty (TransitiveTournament D s) ∧
            ((q : ℝ) ^ (2 * (s - 2)) / 2 ≤
              (@Fintype.card D.vertex D.fintype : ℝ)) ∧
            (ForwardIndependentCount D k : ℝ) ≤
              (32 * Real.rpow (q : ℝ)
                (2 * (s - 2 : Nat) - ((s - 3 : Nat) : ℝ) *
                  (1 - delta / 5))) ^ k := by
-- BODY
  sorry
