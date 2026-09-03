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
  have _hcard := hcard
  have hcount : ((A.product B).filter (fun e => adj e.1 e.2)).card =
      Finset.sum A (fun u => (B.filter (fun v => adj u v)).card) := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    change Finset.sum (A ×ˢ B) (fun a => if adj a.1 a.2 then 1 else 0) = _
    rw [Finset.sum_product A B]
    simp
  have hedge : ((A.product B).filter (fun e => adj e.1 e.2)).card ≤
      (d : ℝ) / (2 * n) * A.card * B.card := by
    calc
      ((A.product B).filter (fun e => adj e.1 e.2)).card =
          Finset.sum A (fun u => ((B.filter (fun v => adj u v)).card : ℝ)) := by
        rw [hcount, Nat.cast_sum]
      _ ≤ Finset.sum A (fun _u => ((d : ℝ) * B.card / (2 * n))) := by
        exact Finset.sum_le_sum (fun u hu => hA u hu)
      _ = (d : ℝ) / (2 * n) * A.card * B.card := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
  have hm := hmix A B
  have hhalf : (d : ℝ) / (2 * n) * A.card * B.card ≤
      |((A.product B).filter (fun e => adj e.1 e.2)).card -
          (d : ℝ) / n * A.card * B.card| := by
    have haux := le_abs_self
      (((d : ℝ) / n * A.card * B.card) -
        ((A.product B).filter (fun e => adj e.1 e.2)).card)
    rw [abs_sub_comm] at haux
    have hrel : (d : ℝ) / (2 * n) * A.card * B.card =
        ((d : ℝ) / n * A.card * B.card) / 2 := by ring
    rw [hrel] at hedge ⊢
    linarith
  have hmain : (d : ℝ) / (2 * n) * A.card * B.card ≤
      lambda * Real.sqrt (A.card * B.card) := le_trans hhalf hm
  have hsquare := Real.sq_sqrt (show (0 : ℝ) ≤ A.card * B.card by positivity)
  have hden : (0 : ℝ) < d := by exact_mod_cast hd
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases hzero : (A.card : ℝ) * B.card = 0
  · simpa [hzero] using (show (0 : ℝ) ≤ 4 * lambda ^ 2 / d ^ 2 * n ^ 2 by positivity)
  · have hpos : 0 < (A.card : ℝ) * B.card :=
      lt_of_le_of_ne (by positivity) (Ne.symm hzero)
    have hleft : 0 ≤ (d : ℝ) / (2 * n) * A.card * B.card := by positivity
    have hsquare' := mul_self_le_mul_self hleft hmain
    field_simp [ne_of_gt hden, ne_of_gt hnreal] at hsquare' ⊢
    have hprod : 0 < (d : ℝ) ^ 2 * ((A.card : ℝ) * B.card) := by positivity
    nlinarith [hsquare, hprod]
