import Tablet.OldPairDigraph
import Tablet.ForwardIndependentCount
import Tablet.RootedTreeCounting
import Tablet.AlonRodlBound

open scoped BigOperators

-- [TABLET NODE: OldCoherentTreeCount]
theorem OldCoherentTreeCount
    (G : LoopGraph) (t q k n h : Nat)
    (ht : 2 ≤ t)
    (hw : 32 * t * q * Nat.log 2 q ≤ k)
    (hmark : ∃ count : (Fin k → Bool) → Nat,
      (∑ z, count z) = ForwardIndependentCount (OldPairDigraph G) k ∧
      (∀ z, count z ≤
        (n ^ 2) ^ (∑ i, (if z i = true then 1 else 0)) *
          h ^ (k - ∑ i, (if z i = true then 1 else 0))) ∧
      (∀ z, count z > 0 →
        (∑ i, (if z i = true then 1 else 0)) ≤ 32 * t * q * Nat.log 2 q))
    (hh : h ≤ n ^ 2) :
    ForwardIndependentCount (OldPairDigraph G) k ≤
      2 ^ k * (n ^ 2) ^ (32 * t * q * Nat.log 2 q) *
        h ^ (k - 32 * t * q * Nat.log 2 q) := by
-- BODY
  sorry
