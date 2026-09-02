import Tablet.Preamble

open scoped BigOperators

-- [TABLET NODE: IncidenceDecayBound]
theorem IncidenceDecayBound
    {V : Type} [Fintype V] [DecidableEq V]
    (adj : V → V → Prop) [DecidableRel adj]
    (q t n d : Nat) (lambda : ℝ)
    (hq : 16 ≤ q) (ht : 2 ≤ t) (hn : 0 < n) (hd : 0 < d)
    (hmix : ∀ A B : Finset V,
      |((A.product B).filter (fun e => adj e.1 e.2)).card -
          (d : ℝ) / n * A.card * B.card| ≤
        lambda * Real.sqrt (A.card * B.card))
    (hupper : (d : ℝ) / n ≤ 4 / q)
    (P Zl Zr : Finset V)
    (hprod : (P.card : ℝ) * Zl.card ≤ 1024 * (q : ℝ) ^ (t + 1))
    (hZ : Zr.card ≤ Zl.card)
    (hdecay : lambda * Real.sqrt ((P.card : ℝ) * Zr.card) ≤
      128 * (q : ℝ) ^ t) :
    (((P.product Zr).filter (fun e => adj e.1 e.2)).card : ℝ) ≤
      5000 * (q : ℝ) ^ t := by
-- BODY
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hZreal : (Zr.card : ℝ) ≤ Zl.card := by exact_mod_cast hZ
  have hprodZr : (P.card : ℝ) * Zr.card ≤ 1024 * (q : ℝ) ^ (t + 1) := by
    calc
      (P.card : ℝ) * Zr.card ≤ (P.card : ℝ) * Zl.card := by
        gcongr
      _ ≤ 1024 * (q : ℝ) ^ (t + 1) := hprod
  have hmain : (d : ℝ) / n * P.card * Zr.card ≤
      4096 * (q : ℝ) ^ t := by
    calc
      (d : ℝ) / n * P.card * Zr.card =
          (d : ℝ) / n * ((P.card : ℝ) * Zr.card) := by ring
      _ ≤ (4 / q) * ((P.card : ℝ) * Zr.card) := by
        gcongr
      _ ≤ (4 / q) * (1024 * (q : ℝ) ^ (t + 1)) := by
        gcongr
      _ = 4096 * (q : ℝ) ^ t := by
        rw [pow_succ]
        field_simp
        ring
  have hmix' := hmix P Zr
  have hcount : (((P.product Zr).filter (fun e => adj e.1 e.2)).card : ℝ) ≤
      (d : ℝ) / n * P.card * Zr.card +
        lambda * Real.sqrt (P.card * Zr.card) := by
    have habs := le_trans (le_abs_self
      (((P.product Zr).filter (fun e => adj e.1 e.2)).card -
        (d : ℝ) / n * P.card * Zr.card)) hmix'
    linarith
  calc
    (((P.product Zr).filter (fun e => adj e.1 e.2)).card : ℝ) ≤
        4096 * (q : ℝ) ^ t + 128 * (q : ℝ) ^ t :=
      hcount.trans (add_le_add hmain hdecay)
    _ ≤ 5000 * (q : ℝ) ^ t := by nlinarith
