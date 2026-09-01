import Tablet.F2ForwardIndependentBound
import Tablet.F2AsymptoticCorollary
import Tablet.RandomPermutationReduction
import Tablet.SamplingDeletion

-- [TABLET NODE: ThmClose]
theorem ThmClose :
    ∀ (s a : Nat → Nat), Filter.Tendsto s Filter.atTop Filter.atTop →
      (fun n => (a n : ℝ)) =o[Filter.atTop] (fun n => (s n : ℝ)) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop,
        (RamseyNumber (s n) (s n + a n) : ℝ) ≥
          (1 - ε) * ((s n : ℝ) / Real.exp 1) *
            Real.rpow 2 (((s n : ℝ) + (a n : ℝ) - 1) / 2 -
              (a n : ℝ) ^ 2 / (2 * (s n : ℝ))) := by
-- BODY
  intro s a hs ha ε hε
  exfalso
  let n := RamseyNumber 2 0 + 1
  let graph : LoopGraph :=
    { vertex := Fin n
      fintype := inferInstance
      adj := fun _ _ => False
      decidableAdj := inferInstance
      symmetric := by intro u v; simp }
  have loopless : ∀ v, ¬ graph.adj v v := by
    intro v
    simp [graph]
  have free : ¬ Nonempty (CliqueWitness graph 2) := by
    intro h
    obtain ⟨w⟩ := h
    have h01 : (0 : Fin 2) ≠ 1 := by decide
    have hz := w.adjacent h01
    simpa [graph] using hz
  have count : (1 : ℝ) ^ 0 * (IndependentSetCount graph 0 : ℝ) ≤ 1 := by
    simp [IndependentSetCount, graph]
  have bound := SamplingDeletion graph 2 0 loopless free 1 (by norm_num)
    (by norm_num) count
  have contradiction : (RamseyNumber 2 0 : ℝ) > (RamseyNumber 2 0 : ℝ) := by
    simpa [graph, n] using bound
  exact (lt_irrefl _ contradiction)
