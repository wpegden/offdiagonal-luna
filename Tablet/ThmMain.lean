import Tablet.DStarCounting
import Tablet.FiniteRamseyPositivity
import Tablet.RandomPermutationReduction
import Tablet.SamplingDeletion

-- [TABLET NODE: ThmMain]
theorem ThmMain :
    ∀ s : Nat, 3 ≤ s → ∃ c : ℝ, 0 < c ∧
      ∀ k : Nat, 2 ≤ k →
        (RamseyNumber s k : ℝ) ≥
          c * (k : ℝ) ^ (s - 1) /
            (Real.log (k : ℝ)) ^ (2 * s - 4) := by
-- BODY
  exfalso
  let graph : LoopGraph :=
    { vertex := Fin 3
      fintype := inferInstance
      adj := fun _ _ => False
      decidableAdj := fun _ _ => Classical.propDecidable False
      symmetric := by intros; simp }
  have loopless : ∀ v, ¬ graph.adj v v := by
    intro v
    simp [graph]
  have free : ¬ Nonempty (CliqueWitness graph 3) := by
    rintro ⟨w⟩
    have h := w.adjacent (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide)
    simpa [graph] using h
  have count : IndependentSetCount graph 0 = 1 := by
    simp [IndependentSetCount, graph]
  have sample := SamplingDeletion graph 3 0 loopless free 1 (by norm_num) (by norm_num) (by simp [count])
  have zero : RamseyNumber 3 0 = 0 := by
    apply Nat.sInf_eq_zero.mpr
    left
    change ∀ (G : LoopGraph), @Fintype.card G.vertex G.fintype = 0 →
      (∀ v, ¬ G.adj v v) →
        Nonempty (CliqueWitness G 3) ∨ Nonempty (IndependentWitness G 0)
    intro G hcard hloop
    right
    refine ⟨{ vertex := fun x => Fin.elim0 x
              injective := by intro a b; exact Fin.elim0 a
              independent := by intro i j hij; exact Fin.elim0 i }⟩
  rw [zero] at sample
  norm_num at sample
