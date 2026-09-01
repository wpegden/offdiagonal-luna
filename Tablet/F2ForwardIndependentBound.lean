import Tablet.F2PairDigraphProperties
import Tablet.F2RankSequenceBound
import Tablet.ForwardIndependentCount

open scoped BigOperators

-- [TABLET NODE: F2ForwardIndependentBound]
theorem F2ForwardIndependentBound (s k : Nat) (hs : 4 ≤ s) (hsk : s ≤ k) :
    ∃ D : LooplessDigraph,
      D = F2PairDigraph s ∧
      ¬ Nonempty (TransitiveTournament D s) ∧
      @Fintype.card D.vertex D.fintype =
        2 ^ (2 * s - 3) - 2 ^ (s - 2) ∧
      (ForwardIndependentCount D k : ℝ) ≤
        (∑ t ∈ Finset.Icc 1 (s - 1),
          (Nat.choose k t *
            2 ^ ((s - 1) * (t + k) - Nat.choose (t + 1) 2) : Nat) : ℝ) := by
-- BODY
  have hp : 1 ≤ s - 1 := by omega
  have hk : 1 ≤ k := by omega
  have hprops := F2PairDigraphProperties s hs
  refine ⟨F2PairDigraph s, rfl, hprops.2.1, hprops.2.2, ?_⟩
  letI := (F2PairDigraph s).fintype
  letI := (F2PairDigraph s).decidableArc
  let Z := { z : (Fin k → (Fin (s - 1) → ZMod 2)) ×
      (Fin k → (Fin (s - 1) → ZMod 2)) //
      ∀ ⦃i j : Fin k⦄, i.val ≤ j.val →
        (∑ r, z.1 i r * z.2 j r) = 1 }
  have binary : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by
    intro x hx
    fin_cases x
    · exact (hx rfl).elim
    · rfl
  have hcard : ForwardIndependentCount (F2PairDigraph s) k ≤ Fintype.card Z := by
    unfold ForwardIndependentCount
    change Fintype.card { f : Fin k → (F2PairDigraph s).vertex //
      ∀ ⦃i j : Fin k⦄, i.val < j.val → ¬ (F2PairDigraph s).arc (f i) (f j) } ≤ Fintype.card Z
    let map : { f : Fin k → (F2PairDigraph s).vertex //
        ∀ ⦃i j : Fin k⦄, i.val < j.val → ¬ (F2PairDigraph s).arc (f i) (f j) } → Z := fun f =>
      ⟨(fun i => (f.1 i).1.1, fun i => (f.1 i).1.2), by
        intro i j hij
        by_cases he : i.val = j.val
        · have hij' : i = j := Fin.ext he
          subst j
          apply binary
          intro hz
          apply (f.1 i).2
          simpa [F2PairDigraph, OldPairDigraph] using hz
        · have hlt : i.val < j.val := lt_of_le_of_ne hij he
          have hn := f.2 hlt
          have hz : (∑ r, (f.1 i).1.1 r * (f.1 j).1.2 r) ≠ 0 := by
            intro hz
            apply hn
            simpa [F2PairDigraph, OldPairDigraph] using hz
          exact binary _ hz⟩
    have hinj : Function.Injective map := by
      intro f g hfg
      apply Subtype.ext
      funext i
      apply Subtype.ext
      have hpairs := congrArg Subtype.val hfg
      exact Prod.ext (congrFun (congrArg Prod.fst hpairs) i)
        (congrFun (congrArg Prod.snd hpairs) i)
    exact Fintype.card_le_of_injective map hinj
  have hbound := F2RankSequenceBound (s - 1) k hp hk
  exact_mod_cast (hcard.trans hbound)
