import Tablet.OldPairDigraph
import Tablet.OldPolarityParameters
import Tablet.ForwardIndependentCount
import Tablet.RootedTreeCounting
import Tablet.AlonRodlBound

open scoped BigOperators

-- [TABLET NODE: OldCoherentTreeCount]
theorem OldCoherentTreeCount
    (K : Type) [Field K] [Fintype K]
    (t q k : Nat) (hqpow : IsPrimePow q) (hq : 16 ≤ q)
    (hK : Fintype.card K = q) (ht : 2 ≤ t) :
    let G := PolarityGraph K t ht
    letI : Fintype G.vertex := G.fintype
    letI : DecidableRel G.adj := G.decidableAdj
    ∀ (n d : Nat) (lambda : ℝ),
      (@Fintype.card G.vertex G.fintype = n ∧
        n = (q ^ (t + 1) - 1) / (q - 1) ∧
        d = (q ^ t - 1) / (q - 1) ∧
        (∀ v : G.vertex, Fintype.card {u : G.vertex // G.adj v u} = d) ∧
        lambda = Real.sqrt ((d : ℝ) -
          ((((q ^ (t - 1) - 1) / (q - 1) : Nat) : ℝ))) ∧
        NonprincipalSpectralBound G lambda ∧
        (q : ℝ) ^ t / 2 ≤ n ∧ (n : ℝ) ≤ 2 * (q : ℝ) ^ t ∧
        (q : ℝ) ^ (t - 1) / 2 ≤ d ∧
        (d : ℝ) ≤ 2 * (q : ℝ) ^ (t - 1) ∧
        lambda ≤ 2 * Real.sqrt d) →
      (∀ A B : Finset G.vertex,
        |((A.product B).filter (fun e => G.adj e.1 e.2)).card -
            (d : ℝ) / n * A.card * B.card| ≤
          lambda * Real.sqrt (A.card * B.card)) →
      0 < n → 0 < d →
      32 * t * q * Nat.log 2 q ≤ k →
      (ForwardIndependentCount (OldPairDigraph G) k : ℝ) ≤
        (8 : ℝ) ^ k * (lambda ^ 2 / d ^ 2) ^
            (k - 32 * t * q * Nat.log 2 q) *
          (n : ℝ) ^ (2 * k) := by
-- BODY
  sorry
