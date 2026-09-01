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
  classical
  let weight : (Fin k → Bool) → Nat := fun z =>
    ∑ i, (if z i = true then 1 else 0)
  have pointwise : ∀ z, count z ≤ Delta ^ w * h ^ (k - w) := by
    intro z
    by_cases hz : count z = 0
    · simp [hz]
    · have hpos : count z > 0 := Nat.pos_of_ne_zero hz
      have hzw : weight z ≤ w := hsupport z hpos
      have hpow : Delta ^ (weight z) * h ^ (k - weight z) ≤
          Delta ^ w * h ^ (k - w) := by
        have hsplit : k - weight z = (k - w) + (w - weight z) := by omega
        rw [hsplit, pow_add]
        have hbase : h ^ (w - weight z) ≤ Delta ^ (w - weight z) := by
          exact Nat.pow_le_pow_left hh _
        calc
          Delta ^ weight z * (h ^ (k - w) * h ^ (w - weight z)) ≤
              Delta ^ weight z * (h ^ (k - w) * Delta ^ (w - weight z)) := by
                exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hbase)
          _ = (Delta ^ weight z * Delta ^ (w - weight z)) * h ^ (k - w) := by
            ac_rfl
          _ = Delta ^ w * h ^ (k - w) := by
            rw [← pow_add, Nat.add_sub_of_le hzw]
      exact (hcount z).trans hpow
  calc
    ∑ z, count z ≤ ∑ z, (Delta ^ w * h ^ (k - w)) :=
      Finset.sum_le_sum (fun z _ => pointwise z)
    _ = 2 ^ k * Delta ^ w * h ^ (k - w) := by
      simp [Fintype.card_fin, Fintype.card_bool]
      ac_rfl
