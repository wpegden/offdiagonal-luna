import Tablet.OldPairDigraph

-- [TABLET NODE: OldPolarityParameters]
theorem OldPolarityParameters (t q : Nat) (ht : 2 ≤ t) (hq : 16 ≤ q) :
    ∃ G : LoopGraph,
      (∀ (a b : Fin (t + 2) → G.vertex),
        (∀ i, ¬ G.adj (a i) (b i)) →
        (∀ ⦃i j : Fin (t + 2)⦄,
          i.val < j.val → G.adj (a i) (b j)) → False) ∧
      ∃ n d : Nat, ∃ lambda : ℝ,
        @Fintype.card G.vertex G.fintype = n ∧
        (q : ℝ) ^ t / 2 ≤ n ∧ (n : ℝ) ≤ 2 * (q : ℝ) ^ t ∧
        (q : ℝ) ^ (t - 1) / 2 ≤ d ∧
          (d : ℝ) ≤ 2 * (q : ℝ) ^ (t - 1) ∧
        lambda ≤ 2 * Real.sqrt d ∧
        ((q : ℝ) ^ (2 * t) / 2 ≤
          (@Fintype.card (OldPairDigraph G).vertex
            (OldPairDigraph G).fintype : ℝ)) := by
-- BODY
  sorry
