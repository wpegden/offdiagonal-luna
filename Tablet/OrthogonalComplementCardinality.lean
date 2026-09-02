import Tablet.Preamble
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.FieldTheory.Finiteness

open scoped LinearAlgebra.Projectivization
open LinearMap (BilinForm)

-- [TABLET NODE: OrthogonalComplementCardinality]
theorem OrthogonalComplementCardinality
    (K V : Type) [Field K] [Fintype K] [AddCommGroup V] [Module K V]
    [Fintype V] (B : BilinForm K V) (hB : B.Nondegenerate)
    (W : Submodule K V) (hK : 2 ≤ Fintype.card K) :
    Module.finrank K (B.orthogonal W) =
        Module.finrank K V - Module.finrank K W ∧
      Nat.card (Projectivization K (B.orthogonal W)) ≤
        2 * Fintype.card K ^ (Module.finrank K (B.orthogonal W) - 1) := by
-- BODY
  constructor
  · exact LinearMap.BilinForm.finrank_orthogonal hB W
  · have hcard : Nat.card (Projectivization K (B.orthogonal W)) =
        (Nat.card (B.orthogonal W) - 1) /
          (Nat.card K - 1) := by
      exact Projectivization.card'' K (B.orthogonal W)
    rw [hcard]
    have hUcard : Nat.card (B.orthogonal W) =
        Nat.card K ^ Module.finrank K (B.orthogonal W) :=
      Module.natCard_eq_pow_finrank (K := K) (V := B.orthogonal W)
    rw [hUcard]
    have hKcard : Nat.card K = Fintype.card K := Nat.card_eq_fintype_card
    rw [hKcard]
    by_cases hr : Module.finrank K (B.orthogonal W) = 0
    · simp [hr]
    · have hrpos : 1 ≤ Module.finrank K (B.orthogonal W) := by omega
      obtain ⟨r, hfin⟩ := Nat.exists_eq_succ_of_ne_zero hr
      rw [hfin]
      rw [pow_succ]
      rw [Nat.succ_sub_one]
      apply (Nat.div_le_iff_le_mul_add_pred (by omega)).2
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
