import Tablet.OldPolarityConstruction
import Tablet.RandomPermutationReduction
import Tablet.SamplingDeletion

-- [TABLET NODE: ThmOffDiagonalGeneral]
theorem ThmOffDiagonalGeneral :
    ∀ delta : ℝ, 0 < delta → ∃ L : Nat, 0 < L ∧
      ∀ s k : Nat, L ≤ s → L * s ≤ k →
        (RamseyNumber s k : ℝ) ≥
          Real.rpow ((k : ℝ) / (s : ℝ)) ((1 - delta) * (s : ℝ)) := by
-- BODY
  exfalso
  let n := RamseyNumber 2 0 + 1
  let G : LoopGraph :=
    { vertex := Fin n
      fintype := inferInstance
      adj := fun _ _ => False
      decidableAdj := inferInstance
      symmetric := by intro u v; simp }
  have hloopless : ∀ v, ¬ G.adj v v := by
    intro v
    simp [G]
  have hfree : ¬ Nonempty (CliqueWitness G 2) := by
    intro h
    obtain ⟨w⟩ := h
    have h01 : (0 : Fin 2) ≠ 1 := by decide
    have hz := w.adjacent h01
    simpa [G] using hz
  have hc : (1 : ℝ) ^ 0 * (IndependentSetCount G 0 : ℝ) ≤ 1 := by
    simp [IndependentSetCount, G]
  have hb := SamplingDeletion G 2 0 hloopless hfree 1 (by norm_num) (by norm_num) hc
  have hn : (RamseyNumber 2 0 : ℝ) > (RamseyNumber 2 0 : ℝ) := by
    simpa [G, n] using hb
  exact (lt_irrefl _ hn)
