import Tablet.Preamble
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.FieldTheory.Finiteness

open scoped LinearAlgebra.Projectivization

-- [TABLET NODE: ProjectiveSpanPointBound]
theorem ProjectiveSpanPointBound
    (K V : Type) [Field K] [Fintype K] [AddCommGroup V] [Module K V]
    [Fintype V] (s : Finset V) :
    Nat.card (Projectivization K (Submodule.span K (s : Set V))) ≤
      Fintype.card K ^ s.card := by
-- BODY
  let W : Submodule K V := Submodule.span K (s : Set V)
  have hspan : Module.finrank K W ≤ s.card := by
    simpa [W] using
      (finrank_span_le_card (R := K) (M := V) (s : Set V))
  have hrep : Function.Injective
      (fun p : Projectivization K W => p.rep) := by
    intro p p' h
    change p.rep = p'.rep at h
    calc
      p = Projectivization.mk K p.rep p.rep_nonzero := p.mk_rep.symm
      _ = Projectivization.mk K p'.rep p'.rep_nonzero := by
        apply (Projectivization.mk_eq_mk_iff' K p.rep p'.rep
          p.rep_nonzero p'.rep_nonzero).2
        exact ⟨1, by simp [h]⟩
      _ = p' := p'.mk_rep
  have hle : Nat.card (Projectivization K W) ≤ Nat.card W := by
    exact Nat.card_le_card_of_injective (fun p : Projectivization K W => p.rep) hrep
  have hWcard : Nat.card W = Nat.card K ^ Module.finrank K W :=
    Module.natCard_eq_pow_finrank
  rw [hWcard] at hle
  have hq : 1 ≤ Nat.card K := by
    exact Nat.one_le_iff_ne_zero.mpr (by simp)
  have hpow : Nat.card K ^ Module.finrank K W ≤ Nat.card K ^ s.card := by
    exact Nat.pow_le_pow_right hq hspan
  have hle' : Nat.card (Projectivization K (Submodule.span K (s : Set V))) ≤
      Nat.card K ^ Module.finrank K W := by
    simpa [W] using hle
  exact hle'.trans (by simpa only [Nat.card_eq_fintype_card] using hpow)
