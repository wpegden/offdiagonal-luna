import Tablet.RamseyNumber

-- [TABLET NODE: FiniteRamseyPositivity]
theorem FiniteRamseyPositivity (s k : Nat) (hs : 2 ≤ s) (hk : 2 ≤ k) :
    0 < RamseyNumber s k := by
-- BODY
  classical
  let Good : Nat → Nat → Nat → Prop := fun a b n =>
    ∀ (G : LoopGraph), n ≤ @Fintype.card G.vertex G.fintype →
      (∀ v, ¬ G.adj v v) →
      Nonempty (CliqueWitness G a) ∨ Nonempty (IndependentWitness G b)
  have hzeroClique : ∀ (b : Nat), Good 0 b 0 := by
    intro b G _ _
    left
    exact ⟨{ vertex := Fin.elim0
             injective := by intro i; exact Fin.elim0 i
             adjacent := by intro i; exact Fin.elim0 i }⟩
  have hzeroIndependent : ∀ (a : Nat), Good a 0 0 := by
    intro a G _ _
    right
    exact ⟨{ vertex := Fin.elim0
             injective := by intro i; exact Fin.elim0 i
             independent := by intro i; exact Fin.elim0 i }⟩
  have ramsey : ∀ a b : Nat, ∃ n, Good a b n := by
    intro a
    induction a with
    | zero =>
        intro b
        exact ⟨0, hzeroClique b⟩
    | succ a iha =>
        intro b
        induction b with
        | zero =>
            exact ⟨0, hzeroIndependent (a + 1)⟩
        | succ b ihb =>
            obtain ⟨nA, hA⟩ := iha (b + 1)
            obtain ⟨nB, hB⟩ := ihb
            refine ⟨nA + nB + 1, ?_⟩
            intro G hcard hloop
            letI : Fintype G.vertex := G.fintype
            letI : DecidableRel G.adj := G.decidableAdj
            have hpos : 0 < nA + nB + 1 := by omega
            have hcardpos : 0 < Fintype.card G.vertex := by omega
            let v : G.vertex := Classical.choice (Fintype.card_pos_iff.mp hcardpos)
            let A : Type := {u : G.vertex // G.adj v u}
            let B : Type := {u : G.vertex // u ≠ v ∧ ¬ G.adj v u}
            let GA : LoopGraph :=
              { vertex := A
                fintype := inferInstance
                adj := fun x y => G.adj x.1 y.1
                decidableAdj := inferInstance
                symmetric := by intro x y; exact G.symmetric _ _ }
            let GB : LoopGraph :=
              { vertex := B
                fintype := inferInstance
                adj := fun x y => G.adj x.1 y.1
                decidableAdj := inferInstance
                symmetric := by intro x y; exact G.symmetric _ _ }
            let e : (Sum (Sum Unit A) B) ≃ G.vertex :=
              { toFun := fun z =>
                  match z with
                  | Sum.inl (Sum.inl _) => v
                  | Sum.inl (Sum.inr x) => x.1
                  | Sum.inr x => x.1
                invFun := fun x =>
                  if hv : x = v then
                    Sum.inl (Sum.inl ())
                  else if ha : G.adj v x then
                    Sum.inl (Sum.inr ⟨x, ha⟩)
                  else
                    Sum.inr ⟨x, ⟨hv, ha⟩⟩
                left_inv := by
                  intro z
                  cases z with
                  | inl z =>
                      cases z with
                      | inl u => simp
                      | inr x =>
                          have hx : ¬ (x.1 = v) := by
                            intro hv
                            apply hloop v
                            simpa [hv] using x.2
                          simp [hx, x.2]
                  | inr x => simp [x.2.1, x.2.2]
                right_inv := by
                  intro x
                  by_cases hv : x = v
                  · simp [hv]
                  · by_cases ha : G.adj v x
                    · simp [hv, ha]
                    · simp [hv, ha] }
            have hcard_split : 1 + Fintype.card A + Fintype.card B = Fintype.card G.vertex := by
              have hc := Fintype.card_congr e
              simpa [Fintype.card_sum, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc
            by_cases hlarge : nA ≤ Fintype.card A
            · have hGA : Nonempty (CliqueWitness GA a) ∨
                  Nonempty (IndependentWitness GA (b + 1)) :=
                hA GA (by simpa [GA] using hlarge) (by
                  intro x hx
                  exact hloop x.1 hx)
              rcases hGA with ⟨⟨c⟩⟩ | ⟨⟨c⟩⟩
              · left
                refine ⟨{
                  vertex := Fin.cases v (fun i : Fin a => (c.vertex i).1)
                  injective := ?_
                  adjacent := ?_
                }⟩
                · intro i j hij
                  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
                  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
                    · rfl
                    · exfalso
                      have hx : G.adj v (c.vertex j).1 := by
                        simpa [GA] using (c.vertex j).property
                      have hvx : v = (c.vertex j).1 := by
                        simpa [Fin.cases_zero, Fin.cases_succ] using hij
                      apply hloop (c.vertex j).1
                      simpa [hvx] using hx
                  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
                    · exfalso
                      have hx : G.adj v (c.vertex i).1 := by
                        simpa [GA] using (c.vertex i).property
                      have hvx : v = (c.vertex i).1 := by
                        simpa [Fin.cases_zero, Fin.cases_succ] using hij.symm
                      apply hloop (c.vertex i).1
                      simpa [hvx] using hx
                    · apply (Fin.succ_inj).2
                      apply c.injective
                      exact Subtype.ext (by
                        simpa [Fin.cases_zero, Fin.cases_succ] using hij)
                · intro i j hij
                  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
                  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
                    · exact (hij rfl).elim
                    · simpa [Fin.cases_zero, Fin.cases_succ, GA] using
                        (c.vertex j).property
                  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
                    · have hx : G.adj v (c.vertex i).1 := by
                        simpa [GA] using (c.vertex i).property
                      exact (G.symmetric _ _).mpr hx
                    · have hne : i ≠ j := by
                        intro h
                        apply hij
                        simpa [h]
                      simpa [Fin.cases_zero, Fin.cases_succ, GA] using c.adjacent hne
              · right
                refine ⟨{
                  vertex := fun i => (c.vertex i).1
                  injective := by
                    intro i j h
                    apply c.injective
                    exact Subtype.ext h
                  independent := by
                    intro i j h
                    simpa [GA] using c.independent h
                }⟩
            · have hAsmall : Fintype.card A < nA := Nat.lt_of_not_ge hlarge
              have hGcard : nA + nB + 1 ≤ 1 + Fintype.card A + Fintype.card B := by
                calc
                  nA + nB + 1 ≤ Fintype.card G.vertex := hcard
                  _ = 1 + Fintype.card A + Fintype.card B := hcard_split.symm
              have hBcard : nB ≤ Fintype.card B := by
                omega
              have hGB : Nonempty (CliqueWitness GB (a + 1)) ∨
                  Nonempty (IndependentWitness GB b) :=
                hB GB (by simpa [GB] using hBcard) (by
                  intro x hx
                  exact hloop x.1 hx)
              rcases hGB with ⟨⟨c⟩⟩ | ⟨⟨c⟩⟩
              · left
                refine ⟨{
                  vertex := fun i => (c.vertex i).1
                  injective := by
                    intro i j h
                    apply c.injective
                    exact Subtype.ext h
                  adjacent := by
                    intro i j h
                    simpa [GB] using c.adjacent h
                }⟩
              · right
                refine ⟨{
                  vertex := Fin.cases v (fun i : Fin b => (c.vertex i).1)
                  injective := ?_
                  independent := ?_
                }⟩
                · intro i j hij
                  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
                  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
                    · rfl
                    · exfalso
                      exact (c.vertex j).property.1 (by
                        simpa [Fin.cases_zero, Fin.cases_succ] using hij.symm)
                  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
                    · exfalso
                      exact (c.vertex i).property.1 (by
                        simpa [Fin.cases_zero, Fin.cases_succ] using hij)
                    · apply (Fin.succ_inj).2
                      apply c.injective
                      exact Subtype.ext (by
                        simpa [Fin.cases_zero, Fin.cases_succ] using hij)
                · intro i j hij
                  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
                  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
                    · exact (hij rfl).elim
                    · exact (c.vertex j).property.2
                  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
                    · intro h
                      apply (c.vertex i).property.2
                      exact (G.symmetric _ _).mp h
                    · have hne : i ≠ j := by
                        intro h
                        apply hij
                        simpa [h]
                      simpa [Fin.cases_zero, Fin.cases_succ, GB] using c.independent hne
  obtain ⟨N, hN⟩ := ramsey s k
  have hmem : N ∈ {n : Nat | ∀ (G : LoopGraph),
      @Fintype.card G.vertex G.fintype = n →
        (∀ v, ¬ G.adj v v) →
        Nonempty (CliqueWitness G s) ∨ Nonempty (IndependentWitness G k)} := by
    intro G hcard hloop
    exact hN G (le_of_eq hcard.symm) hloop
  have hne : ({n : Nat | ∀ (G : LoopGraph),
      @Fintype.card G.vertex G.fintype = n →
        (∀ v, ¬ G.adj v v) →
        Nonempty (CliqueWitness G s) ∨ Nonempty (IndependentWitness G k)} : Set Nat).Nonempty :=
    ⟨N, hmem⟩
  have hzero : (0 : Nat) ∉ {n : Nat | ∀ (G : LoopGraph),
      @Fintype.card G.vertex G.fintype = n →
        (∀ v, ¬ G.adj v v) →
        Nonempty (CliqueWitness G s) ∨ Nonempty (IndependentWitness G k)} := by
    intro h0
    let G0 : LoopGraph :=
      { vertex := Empty
        fintype := inferInstance
        adj := fun _ _ => False
        decidableAdj := inferInstance
        symmetric := by intro; simp }
    have hres := h0 G0 (by simp [G0]) (by
      intro v
      exact Empty.elim v)
    rcases hres with ⟨⟨c⟩⟩ | ⟨⟨c⟩⟩
    · exact (c.vertex ⟨0, by omega⟩).elim
    · exact (c.vertex ⟨0, by omega⟩).elim
  unfold RamseyNumber
  apply (Nat.pos_iff_ne_zero).2
  intro hz
  rcases (Nat.sInf_eq_zero.mp hz) with h0 | hempty
  · exact hzero h0
  · rcases hempty ▸ hne with ⟨x, hx⟩
    simpa using hx
