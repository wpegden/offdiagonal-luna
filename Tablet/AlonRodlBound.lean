import Tablet.ExpanderMixing

-- [TABLET NODE: AlonRodlBound]
theorem AlonRodlBound
    {V : Type} [Fintype V] [DecidableEq V]
    (adj : V → V → Prop) [DecidableRel adj]
    (n d : Nat) (lambda : ℝ)
    (hcard : Fintype.card V = n)
    (hmix : ∀ A B : Finset V,
      |((A.product B).filter (fun e => adj e.1 e.2)).card -
          (d : ℝ) / n * A.card * B.card| ≤
        lambda * Real.sqrt (A.card * B.card))
    (hn : 0 < n) (hd : 0 < d) (A B : Finset V)
    (hA : ∀ u ∈ A,
      ((B.filter (fun v => adj u v)).card : ℝ) ≤
        (d : ℝ) * B.card / (2 * n)) :
    (A.card : ℝ) * B.card ≤ 4 * lambda ^ 2 / d ^ 2 * n ^ 2 := by
-- BODY
  sorry
