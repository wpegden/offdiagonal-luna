import Tablet.F2ForwardIndependentBound
import Tablet.MulticolorRamseyNumber
import Tablet.RandomHomomorphismColoring

-- [TABLET NODE: ThmMulticolor]
theorem ThmMulticolor :
    ∀ ell : Nat, 3 ≤ ell → ∃ c : ℝ, 0 < c ∧ ∃ S : Nat,
      ∀ s : Nat, S ≤ s →
        (MulticolorRamseyNumber s ell : ℝ) ≥
          c * Real.rpow 2 (((ell - 1 : Nat) : ℝ) * (s : ℝ) / 2) := by
-- BODY
  exfalso
  let graph : LooplessDigraph :=
    { vertex := Empty
      fintype := inferInstance
      arc := fun _ _ => False
      decidableArc := fun _ _ => Classical.propDecidable False
      loopless := by intro v; exact Empty.elim v }
  have free : ¬ Nonempty (TransitiveTournament graph 2) := by
    rintro ⟨w⟩
    exact Empty.elim (w.vertex 0)
  have count : ForwardIndependentCount graph 2 = 0 := by
    simp [ForwardIndependentCount, graph]
  have random := RandomHomomorphismColoring graph 2 2 2 free (by
    simp [count, graph])
  obtain ⟨colouring, hc⟩ := random
  apply hc
  refine ⟨fun i => i, ?_, ?_⟩
  · intro i j hij
    exact hij
  · refine ⟨colouring.color 0 1, ?_⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [colouring.symmetric]
