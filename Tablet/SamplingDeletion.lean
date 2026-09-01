import Tablet.CliqueWitness
import Tablet.IndependentSetCount
import Tablet.RamseyNumber

-- [TABLET NODE: SamplingDeletion]
theorem SamplingDeletion
    (G : LoopGraph) (s k : Nat)
    (hloopless : ∀ v, ¬ G.adj v v)
    (hfree : ¬ Nonempty (CliqueWitness G s))
    (hk : 1 ≤ k)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hcount : p ^ k * (IndependentSetCount G k : ℝ) ≤ 1) :
    (RamseyNumber s k : ℝ) >
      p * (@Fintype.card G.vertex G.fintype : ℝ) - 1 := by
-- BODY
  sorry
