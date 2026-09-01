import Tablet.Preamble

open scoped BigOperators

-- [TABLET NODE: RootedTreeCounting]
theorem RootedTreeCounting
    (k w Delta h : Nat)
    (count : (Fin k → Bool) → Nat)
    (hcount : ∀ z,
      count z ≤ Delta ^ (∑ i, (if z i = true then 1 else 0)) *
        h ^ (k - ∑ i, (if z i = true then 1 else 0)))
    (hsupport : ∀ z, count z > 0 →
      (∑ i, (if z i = true then 1 else 0)) ≤ w)
    (hh : h ≤ Delta) (hw : w ≤ k) :
    (∑ z, count z) ≤ 2 ^ k * Delta ^ w * h ^ (k - w) := by
-- BODY
  sorry
