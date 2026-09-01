import Tablet.OldPairDigraph
import Tablet.NonprincipalSpectralBound
import Tablet.PolarityGraph
import Mathlib.Algebra.IsPrimePow

-- [TABLET NODE: OldPolarityParameters]
theorem OldPolarityParameters
    (K : Type) [Field K] [Fintype K]
    (t q : Nat) (ht : 2 ≤ t) (hqpow : IsPrimePow q) (hq : 16 ≤ q)
    (hK : Fintype.card K = q) :
    let G := PolarityGraph K t ht
    letI : Fintype G.vertex := G.fintype
    letI : DecidableRel G.adj := G.decidableAdj
    (∀ (a b : Fin (t + 2) → G.vertex),
      (∀ i, ¬ G.adj (a i) (b i)) →
      (∀ ⦃i j : Fin (t + 2)⦄,
        i.val < j.val → G.adj (a i) (b j)) → False) ∧
    ∃ n d : Nat, ∃ lambda : ℝ,
      @Fintype.card G.vertex G.fintype = n ∧
      n = (q ^ (t + 1) - 1) / (q - 1) ∧
      d = (q ^ t - 1) / (q - 1) ∧
        (∀ v : G.vertex, Fintype.card {u : G.vertex // G.adj v u} = d) ∧
        lambda = Real.sqrt ((d : ℝ) -
          ((((q ^ (t - 1) - 1) / (q - 1) : Nat) : ℝ))) ∧
        NonprincipalSpectralBound G lambda ∧
      (q : ℝ) ^ t / 2 ≤ n ∧ (n : ℝ) ≤ 2 * (q : ℝ) ^ t ∧
      (q : ℝ) ^ (t - 1) / 2 ≤ d ∧
        (d : ℝ) ≤ 2 * (q : ℝ) ^ (t - 1) ∧
      lambda ≤ 2 * Real.sqrt d ∧
      ((q : ℝ) ^ (2 * t) / 2 ≤
        (@Fintype.card (OldPairDigraph G).vertex
          (OldPairDigraph G).fintype : ℝ)) := by
-- BODY
  sorry
