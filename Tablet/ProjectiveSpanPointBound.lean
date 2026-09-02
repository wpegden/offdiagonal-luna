import Tablet.Preamble
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.FieldTheory.Finiteness

open scoped LinearAlgebra.Projectivization

-- [TABLET NODE: ProjectiveSpanPointBound]
theorem ProjectiveSpanPointBound
    (K V : Type) [Field K] [Fintype K] [AddCommGroup V] [Module K V]
    [Fintype V] (s : Finset V) :
    Nat.card (Projectivization K (Submodule.span K (s : Set V))) =
        (Fintype.card K ^ Module.finrank K
            (Submodule.span K (s : Set V)) - 1) /
          (Fintype.card K - 1) ∧
      (Module.finrank K (Submodule.span K (s : Set V)) = 0 →
        Nat.card (Projectivization K (Submodule.span K (s : Set V))) = 0) ∧
      (1 ≤ Module.finrank K (Submodule.span K (s : Set V)) →
        Nat.card (Projectivization K (Submodule.span K (s : Set V))) ≤
          2 * Fintype.card K ^
            (Module.finrank K (Submodule.span K (s : Set V)) - 1)) := by
-- BODY
  let W : Submodule K V := Submodule.span K (s : Set V)
  have hcard : Nat.card (Projectivization K W) =
      (Nat.card W - 1) / (Nat.card K - 1) := by
    exact Projectivization.card'' K W
  have hWcard : Nat.card W = Nat.card K ^ Module.finrank K W :=
    Module.natCard_eq_pow_finrank
  have hKcard : Nat.card K = Fintype.card K := Nat.card_eq_fintype_card
  have hexact : Nat.card (Projectivization K W) =
      (Fintype.card K ^ Module.finrank K W - 1) /
        (Fintype.card K - 1) := by
    rw [hcard, hWcard, hKcard]
  have hKpos : 0 < Fintype.card K := by
    exact Fintype.card_pos_iff.mpr inferInstance
  have hKtwo : 2 ≤ Fintype.card K := by
    have hlt : 1 < Nat.card K := Finite.one_lt_card
    have hlt' : 1 < Fintype.card K := by simpa [hKcard] using hlt
    omega
  refine ⟨?_, ?_, ?_⟩
  · simpa [W] using hexact
  · intro hr
    simpa [W, hr] using hexact
  · intro hr
    have hbound : Nat.card (Projectivization K W) ≤
        2 * Fintype.card K ^ (Module.finrank K W - 1) := by
      rw [hexact]
      have hr' : ∃ r : Nat, Module.finrank K W = r + 1 := by
        exact ⟨Module.finrank K W - 1, (Nat.sub_add_cancel hr).symm⟩
      obtain ⟨r, hfin⟩ := hr'
      rw [hfin, pow_succ, Nat.succ_sub_one]
      apply (Nat.div_le_iff_le_mul_add_pred (by omega : 0 < Fintype.card K - 1)).2
      have hbig : Fintype.card K ^ r * Fintype.card K - 1 ≤
          (2 * Fintype.card K ^ r) * (Fintype.card K - 1) := by
        calc
          Fintype.card K ^ r * Fintype.card K - 1 ≤
              Fintype.card K ^ r * Fintype.card K := Nat.sub_le _ _
          _ ≤ Fintype.card K ^ r * (2 * (Fintype.card K - 1)) := by
            apply Nat.mul_le_mul_left
            omega
          _ = (2 * Fintype.card K ^ r) * (Fintype.card K - 1) := by ring
      calc
        Fintype.card K ^ r * Fintype.card K - 1 ≤
            (2 * Fintype.card K ^ r) * (Fintype.card K - 1) := hbig
        _ ≤ (Fintype.card K - 1) * (2 * Fintype.card K ^ r) +
            (Fintype.card K - 1 - 1) := by
              have hcomm :
                  (2 * Fintype.card K ^ r) * (Fintype.card K - 1) =
                    (Fintype.card K - 1) * (2 * Fintype.card K ^ r) :=
                Nat.mul_comm _ _
              calc
                (2 * Fintype.card K ^ r) * (Fintype.card K - 1) ≤
                    (2 * Fintype.card K ^ r) * (Fintype.card K - 1) +
                      (Fintype.card K - 1) - 1 := by omega
                _ = (Fintype.card K - 1) * (2 * Fintype.card K ^ r) +
                    (Fintype.card K - 1) - 1 := by rw [hcomm]
                _ = (Fintype.card K - 1) * (2 * Fintype.card K ^ r) +
                    (Fintype.card K - 1 - 1) := by omega
    simpa [W] using hbound
