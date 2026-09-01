import Tablet.Preamble

open scoped BigOperators

-- [TABLET NODE: ExpanderMixing]
theorem ExpanderMixing
    {V : Type} [Fintype V] [DecidableEq V]
    (adj : V → V → Prop) [DecidableRel adj]
    (n d : Nat) (lambda : ℝ)
    (hcard : Fintype.card V = n)
    (hspectral : ∀ x y : V → ℝ,
      |(∑ u, ∑ v, x u * (if adj u v then 1 else 0) * y v) -
          (d : ℝ) / n * (∑ u, x u) * (∑ v, y v)| ≤
        lambda * Real.sqrt ((∑ u, (x u) ^ 2) * (∑ v, (y v) ^ 2))) :
    ∀ A B : Finset V,
      |((A.product B).filter (fun e => adj e.1 e.2)).card -
          (d : ℝ) / n * A.card * B.card| ≤
        lambda * Real.sqrt (A.card * B.card) := by
-- BODY
  sorry
