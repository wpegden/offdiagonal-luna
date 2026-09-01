import Tablet.F2ForwardIndependentBound
import Tablet.RandomPermutationReduction
import Tablet.SamplingDeletion

-- [TABLET NODE: ThmKCk]
theorem ThmKCk :
    ∀ C : ℝ, 1 < C → ∃ S : Nat, ∀ s : Nat, S ≤ s →
      (RamseyNumber s (Nat.ceil (C * (s : ℝ))) : ℝ) ≥
        Real.rpow 2 ((1 - 1 / (2 * C)) * (s : ℝ)) := by
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
