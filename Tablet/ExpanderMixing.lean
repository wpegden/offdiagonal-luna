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
  have _hcard := hcard
  intro A B
  have h := hspectral (fun u => if u ∈ A then 1 else 0)
    (fun v => if v ∈ B then 1 else 0)
  have hcountNat :
      (∑ x, (∑ y ∈ B, if adj x y then (if x ∈ A then 1 else 0) else 0)) =
        ((A.product B).filter (fun e => adj e.1 e.2)).card := by
    rw [Finset.card_filter]
    change (∑ x, (∑ y ∈ B, if adj x y then (if x ∈ A then 1 else 0) else 0)) =
      ∑ x ∈ A ×ˢ B, if adj x.1 x.2 then 1 else 0
    rw [Finset.sum_product' A B (fun x y => if adj x y then 1 else 0)]
    have pointwise (x y : V) :
        (if adj x y then (if x ∈ A then 1 else 0) else 0) =
          (if x ∈ A then (if adj x y then 1 else 0) else 0) := by
      by_cases hx : x ∈ A <;> simp [hx]
    simp_rw [pointwise, Finset.sum_ite_irrel]
    simp [Finset.sum_boole, Finset.sum_filter]
  have hcount :
      (∑ x, (∑ y ∈ B, if adj x y then (if x ∈ A then (1 : ℝ) else 0) else 0)) =
        (((A.product B).filter (fun e => adj e.1 e.2)).card : ℝ) := by
    exact_mod_cast hcountNat
  norm_num at h ⊢
  rw [hcount] at h
  simpa [Finset.sum_boole] using h
