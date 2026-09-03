import Tablet.CliqueWitness
import Tablet.IndependentSetCount
import Tablet.RamseyNumber
import Tablet.FiniteRamseyPositivity
import Mathlib.Algebra.BigOperators.Ring.Finset

-- [TABLET NODE: SamplingDeletion]
theorem SamplingDeletion
    (G : LoopGraph) (s k : Nat)
    (hloopless : ∀ v, ¬ G.adj v v)
    (hfree : ¬ Nonempty (CliqueWitness G s))
    (hk : 1 ≤ k)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hcount : p ^ k * (IndependentSetCount G k : ℝ) ≤ 1) :
    (RamseyNumber s k : ℝ) >
      p * (@Fintype.card G.vertex G.fintype : ℝ) - 1 := by
-- BODY
  classical
  letI := G.fintype
  letI := Classical.decEq G.vertex
  letI := G.decidableAdj
  have hs0 : s ≠ 0 := by
    intro hs
    apply hfree
    subst s
    exact ⟨{ vertex := Fin.elim0
             injective := by intro i; exact Fin.elim0 i
             adjacent := by intro i; exact Fin.elim0 i }⟩
  let ip : Finset G.vertex → Prop := fun S =>
    S.card = k ∧ ∀ ⦃u v : G.vertex⦄, u ∈ S → v ∈ S → u ≠ v → ¬ G.adj u v
  let Fam := { S : Finset G.vertex // ip S }
  letI : Fintype Fam :=
    Fintype.subtype (Finset.univ.filter ip) (by intro S; simp [ip])
  have hFam : Fintype.card Fam = IndependentSetCount G k := by
    change Fintype.card { S : Finset G.vertex // ip S } = _
    rfl
  let V : Finset G.vertex := Finset.univ
  let w : Finset G.vertex → ℝ := fun U =>
    (∏ x ∈ U, p) * (∏ x ∈ V \ U, (1 - p))
  have hweighted (B : Finset G.vertex) :
      (∑ U ∈ V.powerset, (if B ⊆ U then w U else 0)) = ∏ x ∈ B, p := by
    have hprod (T : Finset G.vertex) :
        (∑ U ∈ T.powerset,
          (∏ x ∈ U, p) * (∏ x ∈ T \ U, (1 - p))) = 1 := by
      have h := Finset.prod_add (fun _ : G.vertex => p)
        (fun _ : G.vertex => (1 - p)) T
      simpa [Finset.prod_const, sub_eq_add_neg] using h.symm
    let S : Finset (Finset G.vertex) := (V.powerset).filter (B ⊆ ·)
    let T : Finset G.vertex := V \ B
    have hTU (U : Finset G.vertex) (hU : U ∈ T.powerset) : U ⊆ V \ B := by
      simpa [T] using Finset.mem_powerset.1 hU
    have hsum_bij :
        (∑ U ∈ T.powerset, w (B ∪ U)) = ∑ U ∈ S, w U := by
      apply Finset.sum_bij (fun U _ => B ∪ U)
      · intro U hU
        apply Finset.mem_filter.2
        refine ⟨Finset.mem_powerset.2 ?_, ?_⟩
        · intro x hx
          have hUV : U ⊆ V := by
            intro y hy
            exact (Finset.mem_sdiff.1 (hTU U hU hy)).1
          rcases Finset.mem_union.1 hx with hxB | hxU
          · simpa [V] using (Finset.mem_univ x)
          · exact hUV hxU
        · intro x hx
          exact Finset.mem_union_left U hx
      · intro U hU U' hU' heq
        apply Finset.Subset.antisymm
        · intro x hx
          have hx' : x ∈ B ∪ U' := by
            rw [← heq]
            exact Finset.mem_union_right B hx
          rcases Finset.mem_union.1 hx' with hxB | hxU'
          · exact ((Finset.mem_sdiff.1 (hTU U hU hx)).2 hxB).elim
          · exact hxU'
        · intro x hx
          have hx' : x ∈ B ∪ U := by
            rw [heq]
            exact Finset.mem_union_right B hx
          rcases Finset.mem_union.1 hx' with hxB | hxU
          · exact ((Finset.mem_sdiff.1 (hTU U' hU' hx)).2 hxB).elim
          · exact hxU
      · intro U hU
        have hU' : U ∈ V.powerset ∧ B ⊆ U := by
          simpa [S] using hU
        refine ⟨U \ B, ?_, ?_⟩
        · apply Finset.mem_powerset.2
          change U \ B ⊆ V \ B
          intro x hx
          exact Finset.mem_sdiff.2 ⟨Finset.mem_powerset.1 hU'.1
              (Finset.mem_sdiff.1 hx).1, (Finset.mem_sdiff.1 hx).2⟩
        · exact Finset.union_sdiff_of_subset hU'.2
      · intro U hU
        rfl
    calc
      (∑ U ∈ V.powerset, (if B ⊆ U then w U else 0)) = ∑ U ∈ S, w U := by
        rw [Finset.sum_filter]
      _ = ∑ U ∈ T.powerset, w (B ∪ U) := hsum_bij.symm
      _ = (∏ x ∈ B, p) *
          ∑ U ∈ T.powerset,
            (∏ x ∈ U, p) * (∏ x ∈ T \ U, (1 - p)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro U hU
        have hdisj : Disjoint B U := Finset.disjoint_left.2 (by
          intro x hxB hxU
          exact (Finset.mem_sdiff.1 (hTU U hU hxU)).2 hxB)
        simp only [w, Finset.prod_union hdisj]
        have hcomp : V \ (B ∪ U) = T \ U := by
          ext x
          simp [T, and_assoc]
        rw [hcomp]
        ring
      _ = ∏ x ∈ B, p := by rw [hprod T, mul_one]
  have hweight : (∑ U ∈ V.powerset, w U) = 1 := by
    simpa using hweighted (∅ : Finset G.vertex)
  have hw_nonneg : ∀ U ∈ V.powerset, 0 ≤ w U := by
    intro U hU
    apply mul_nonneg
    · exact Finset.prod_nonneg (by intro x hx; exact hp0)
    · apply Finset.prod_nonneg
      intro x hx
      linarith
  have hw_exists : ∃ U ∈ V.powerset, 0 < w U := by
    by_cases hp : p = 0
    · subst p
      refine ⟨∅, Finset.empty_mem_powerset V, ?_⟩
      simp [w]
    · by_cases hp' : p = 1
      · subst p
        refine ⟨V, Finset.mem_powerset.2 (by rfl), ?_⟩
        simp [w]
      · have hpp : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hp)
        have hq : 0 < 1 - p := sub_pos.mpr (lt_of_le_of_ne hp1 hp')
        refine ⟨∅, Finset.empty_mem_powerset V, ?_⟩
        simp [w, hq]
  have haverage : ∃ U ∈ V.powerset,
      p * (V.card : ℝ) - p ^ k * (Fintype.card Fam : ℝ) ≤
        (U.card : ℝ) -
          (((Finset.univ : Finset Fam).filter (fun i => i.1 ⊆ U)).card : ℝ) := by
    let f : Finset G.vertex → ℝ := fun U =>
      (U.card : ℝ) -
        (((Finset.univ : Finset Fam).filter (fun i => i.1 ⊆ U)).card : ℝ)
    have hsize :
        (∑ U ∈ V.powerset, w U * (U.card : ℝ)) = p * (V.card : ℝ) := by
      have hcard (U : Finset G.vertex) (hU : U ∈ V.powerset) :
          (U.card : ℝ) = ∑ x ∈ V, if x ∈ U then 1 else 0 := by
        have hUV : U ⊆ V := Finset.mem_powerset.1 hU
        have hfilter : V.filter (fun x => x ∈ U) = U := by
          ext x
          by_cases hx : x ∈ U
          · simp [hx, hUV hx]
          · simp [hx]
        calc
          (U.card : ℝ) = ∑ x ∈ U, (1 : ℝ) := by simp
          _ = ∑ x ∈ V.filter (fun x => x ∈ U), (1 : ℝ) := by rw [hfilter]
          _ = ∑ x ∈ V, if x ∈ U then 1 else 0 := by rw [Finset.sum_filter]
      calc
        (∑ U ∈ V.powerset, w U * (U.card : ℝ)) =
            ∑ U ∈ V.powerset, w U *
              (∑ x ∈ V, if x ∈ U then 1 else 0) := by
                apply Finset.sum_congr rfl
                intro U hU
                rw [hcard U hU]
        _ = ∑ x ∈ V, ∑ U ∈ V.powerset,
              w U * (if x ∈ U then 1 else 0) := by
                simp_rw [Finset.mul_sum]
                rw [Finset.sum_comm]
        _ = ∑ x ∈ V, p := by
          apply Finset.sum_congr rfl
          intro x hx
          have hsingle := hweighted ({x} : Finset G.vertex)
          simpa [Finset.singleton_subset_iff, mul_ite] using hsingle
        _ = p * (V.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
    have hbad :
        (∑ U ∈ V.powerset,
          w U * (((Finset.univ : Finset Fam).filter
            (fun i => i.1 ⊆ U)).card : ℝ)) =
          p ^ k * (Fintype.card Fam : ℝ) := by
      have hbadcard (U : Finset G.vertex) :
          (((Finset.univ : Finset Fam).filter (fun i => i.1 ⊆ U)).card : ℝ) =
            ∑ i ∈ (Finset.univ : Finset Fam), if i.1 ⊆ U then 1 else 0 := by
        rw [Finset.card_filter]
        norm_cast
      calc
        (∑ U ∈ V.powerset,
            w U * (((Finset.univ : Finset Fam).filter
              (fun i => i.1 ⊆ U)).card : ℝ)) =
            ∑ U ∈ V.powerset, w U *
              (∑ i ∈ (Finset.univ : Finset Fam), if i.1 ⊆ U then 1 else 0) := by
                apply Finset.sum_congr rfl
                intro U hU
                rw [hbadcard U]
        _ = ∑ i ∈ (Finset.univ : Finset Fam),
              ∑ U ∈ V.powerset, w U * (if i.1 ⊆ U then 1 else 0) := by
                simp_rw [Finset.mul_sum]
                rw [Finset.sum_comm]
        _ = ∑ i ∈ (Finset.univ : Finset Fam), p ^ k := by
          apply Finset.sum_congr rfl
          intro i hi
          have hiweighted := hweighted i.1
          have hicard := i.2.1
          simpa [hicard, mul_ite] using hiweighted
        _ = p ^ k * (Fintype.card Fam : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
          ring
    have hsumf : (∑ U ∈ V.powerset, w U * f U) =
        p * (V.card : ℝ) - p ^ k * (Fintype.card Fam : ℝ) := by
      simp only [f]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, hsize, hbad]
    by_contra hn
    push_neg at hn
    obtain ⟨U0, hU0, hw0⟩ := hw_exists
    have hlt :
        (∑ U ∈ V.powerset, w U * f U) <
          ∑ U ∈ V.powerset, w U *
            (p * (V.card : ℝ) - p ^ k * (Fintype.card Fam : ℝ)) := by
      apply Finset.sum_lt_sum
      · intro U hU
        exact mul_le_mul_of_nonneg_left (le_of_lt (hn U hU)) (hw_nonneg U hU)
      · exact ⟨U0, hU0, mul_lt_mul_of_pos_left (hn U0 hU0) hw0⟩
    rw [← Finset.sum_mul, hweight, one_mul] at hlt
    exact (not_lt_of_ge (le_of_eq hsumf.symm)) hlt
  obtain ⟨U, hU, hUbound⟩ := haverage
  have hcountFam : p ^ k * (Fintype.card Fam : ℝ) ≤ 1 := by
    simpa [hFam] using hcount
  have hlower : p * (V.card : ℝ) - 1 ≤
      (U.card : ℝ) -
        (((Finset.univ : Finset Fam).filter (fun i => i.1 ⊆ U)).card : ℝ) := by
    linarith
  let L : Finset Fam := (Finset.univ : Finset Fam).filter (fun i => i.1 ⊆ U)
  have hhit : ∀ (L : Finset Fam),
      (∀ i ∈ L, (i.1).Nonempty) →
        ∃ D : Finset G.vertex, D.card ≤ L.card ∧
          ∀ i ∈ L, ¬ Disjoint i.1 D := by
    intro L
    induction L using Finset.induction_on with
    | empty =>
        intro _
        refine ⟨∅, by simp, ?_⟩
        simp
    | @insert a L ha ih =>
        intro hnon
        obtain ⟨x, hx⟩ := hnon a (Finset.mem_insert_self a L)
        obtain ⟨D, hDcard, hDhit⟩ := ih (by
          intro i hi
          exact hnon i (Finset.mem_insert_of_mem hi))
        refine ⟨insert x D, ?_, ?_⟩
        · calc
            (insert x D).card ≤ D.card + 1 := Finset.card_insert_le x D
            _ ≤ L.card + 1 := Nat.add_le_add_right hDcard 1
            _ = (insert a L).card := (Finset.card_insert_of_notMem ha).symm
        · intro i hi
          by_cases hia : i = a
          · subst i
            intro hdis
            exact (Finset.disjoint_left.1 hdis) hx
              (Finset.mem_insert_self x D)
          · intro hdis
            apply hDhit i (by simpa [hia] using hi)
            apply Finset.disjoint_left.2
            intro y hy hyD
            exact Finset.disjoint_left.1 hdis hy
              (Finset.mem_insert_of_mem hyD)
  have hnon (i : Fam) (hi : i ∈ L) : (i.1).Nonempty := by
    apply Finset.card_pos.mp
    rw [i.2.1]
    exact hk
  obtain ⟨D, hDcard, hDhit⟩ := hhit L hnon
  have hD : ∀ S : Finset G.vertex, S.card = k →
      (∀ ⦃u v : G.vertex⦄, u ∈ S → v ∈ S → u ≠ v → ¬ G.adj u v) →
      S ⊆ U → ¬ Disjoint S D := by
    intro S hScard hSind hSsub
    let i : Fam := ⟨S, ⟨hScard, hSind⟩⟩
    apply hDhit i
    exact Finset.mem_filter.2 ⟨Finset.mem_univ i, hSsub⟩
  let D0 : Finset G.vertex := U ∩ D
  let H : LoopGraph :=
    { vertex := {v : G.vertex // v ∈ U \ D0}
      fintype := inferInstance
      adj := fun x y => G.adj x.1 y.1
      decidableAdj := inferInstance
      symmetric := by intro x y; exact G.symmetric _ _ }
  have hcardH : @Fintype.card H.vertex H.fintype = U.card - D0.card := by
    change Fintype.card (↥(U \ D0)) = _
    rw [Fintype.card_coe]
    rw [Finset.card_sdiff_of_subset Finset.inter_subset_left]
  have hD0 : D0.card ≤ D.card := by
    dsimp [D0]
    exact Finset.card_le_card Finset.inter_subset_right
  have hcard_lower : @Fintype.card H.vertex H.fintype ≥ U.card - D.card := by
    rw [hcardH]
    omega
  have hloopH : ∀ v, ¬ H.adj v v := by
    intro v hv
    exact hloopless v.1 hv
  have hcliqueH : ¬ Nonempty (CliqueWitness H s) := by
    rintro ⟨c⟩
    apply hfree
    let v : Fin s → G.vertex := fun i => (c.vertex i).1
    have hv : Function.Injective v := by
      intro i j hij
      apply c.injective
      exact Subtype.ext hij
    have ha : ∀ ⦃i j : Fin s⦄, i ≠ j → G.adj (v i) (v j) := by
      intro i j hij
      exact c.adjacent hij
    exact ⟨{ vertex := v, injective := hv, adjacent := ha }⟩
  have hindH : ¬ Nonempty (IndependentWitness H k) := by
    rintro ⟨c⟩
    let S : Finset G.vertex := Finset.univ.image (fun i : Fin k => (c.vertex i).1)
    have hSinj : Function.Injective (fun i : Fin k => (c.vertex i).1) := by
      intro i j hij
      apply c.injective
      exact Subtype.ext hij
    have hScard : S.card = k := by
      rw [Finset.card_image_iff.mpr]
      · simp
      · intro i hi j hj hij
        exact hSinj hij
    have hSind : ∀ ⦃u v : G.vertex⦄, u ∈ S → v ∈ S → u ≠ v → ¬ G.adj u v := by
      intro u v hu hv huv hadj
      rw [Finset.mem_image] at hu hv
      obtain ⟨i, hi, rfl⟩ := hu
      obtain ⟨j, hj, rfl⟩ := hv
      apply (c.independent (i := i) (j := j))
      intro hij
      apply huv
      exact congrArg (fun z : Fin k => (c.vertex z).1) hij
      simpa [H] using hadj
    have hSsub : S ⊆ U := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      exact (Finset.mem_sdiff.1 (c.vertex i).property).1
    have hnot : ¬ Disjoint S D := hD S hScard hSind hSsub
    apply hnot
    apply Finset.disjoint_left.2
    intro x hxS hxD
    rw [Finset.mem_image] at hxS
    obtain ⟨i, hi, rfl⟩ := hxS
    have hxH : (c.vertex i).1 ∉ D0 :=
      (Finset.mem_sdiff.1 (c.vertex i).property).2
    exact hxH (Finset.mem_inter.2 ⟨
      (Finset.mem_sdiff.1 (c.vertex i).property).1, hxD⟩)
  have hHm : p * (V.card : ℝ) - 1 ≤
      (@Fintype.card H.vertex H.fintype : ℝ) := by
    have hLreal : p * (V.card : ℝ) - 1 ≤
        (U.card : ℝ) -
          (((Finset.univ : Finset Fam).filter
            (fun i => i.1 ⊆ U)).card : ℝ) := by
      simpa using hlower
    have hDreal : (D.card : ℝ) ≤
        (((Finset.univ : Finset Fam).filter
          (fun i => i.1 ⊆ U)).card : ℝ) := by
      exact_mod_cast hDcard
    have hD0real : (D0.card : ℝ) ≤ (D.card : ℝ) := by
      exact_mod_cast hD0
    have hUD : (U.card : ℝ) -
          (((Finset.univ : Finset Fam).filter
            (fun i => i.1 ⊆ U)).card : ℝ) ≤
        (U.card : ℝ) - (D0.card : ℝ) := by
      linarith
    rw [hcardH]
    have hD0U : D0.card ≤ U.card := by
      exact Finset.card_le_card Finset.inter_subset_left
    rw [Nat.cast_sub hD0U]
    exact hLreal.trans hUD
  have hRnonempty :
      ({n : Nat | ∀ (J : LoopGraph),
        @Fintype.card J.vertex J.fintype = n →
        (∀ v, ¬ J.adj v v) →
        Nonempty (CliqueWitness J s) ∨ Nonempty (IndependentWitness J k)} : Set Nat).Nonempty := by
    by_cases hk1 : k = 1
    · refine ⟨1, ?_⟩
      intro J hcard hloopJ
      letI := J.fintype
      letI := J.decidableAdj
      subst k
      right
      have hpos : 0 < Fintype.card J.vertex := by omega
      let v : J.vertex := Classical.choice (Fintype.card_pos_iff.mp hpos)
      have hv : Function.Injective (fun _ : Fin 1 => v) := by
        intro i j _
        exact Subsingleton.elim _ _
      have hi : ∀ ⦃i j : Fin 1⦄, i ≠ j → ¬ J.adj v v := by
        intro i j hij
        exact (hij (Subsingleton.elim _ _)).elim
      exact ⟨{ vertex := (fun _ : Fin 1 => v), injective := hv, independent := hi }⟩
    · by_cases hs1 : s = 1
      · refine ⟨1, ?_⟩
        intro J hcard hloopJ
        letI := J.fintype
        letI := J.decidableAdj
        subst s
        left
        have hpos : 0 < Fintype.card J.vertex := by omega
        let v : J.vertex := Classical.choice (Fintype.card_pos_iff.mp hpos)
        have hv : Function.Injective (fun _ : Fin 1 => v) := by
          intro i j _
          exact Subsingleton.elim _ _
        have ha : ∀ ⦃i j : Fin 1⦄, i ≠ j → J.adj v v := by
          intro i j hij
          exact (hij (Subsingleton.elim _ _)).elim
        exact ⟨{ vertex := (fun _ : Fin 1 => v), injective := hv, adjacent := ha }⟩
      · have hs2 : 2 ≤ s := by omega
        have hk2 : 2 ≤ k := by omega
        exact Nat.nonempty_of_pos_sInf (FiniteRamseyPositivity s k hs2 hk2)
  have hRmem : ∀ (J : LoopGraph),
      @Fintype.card J.vertex J.fintype = RamseyNumber s k →
      (∀ v, ¬ J.adj v v) →
      Nonempty (CliqueWitness J s) ∨ Nonempty (IndependentWitness J k) := by
    have h := Nat.sInf_mem hRnonempty
    simpa [RamseyNumber] using h
  by_contra hnot
  have hle : (RamseyNumber s k : ℝ) ≤
      (@Fintype.card H.vertex H.fintype : ℝ) :=
    le_trans (le_of_not_gt hnot) hHm
  have hleN : RamseyNumber s k ≤ @Fintype.card H.vertex H.fintype := by
    exact_mod_cast hle
  let e : H.vertex ≃ Fin (@Fintype.card H.vertex H.fintype) :=
    Fintype.equivFin H.vertex
  let ι : Fin (RamseyNumber s k) → H.vertex :=
    fun i => e.symm (Fin.castLE hleN i)
  have hι : Function.Injective ι := by
    intro i j hij
    have hcast : Fin.castLE hleN i = Fin.castLE hleN j := by
      simpa [ι] using congrArg e hij
    apply Fin.ext
    simpa [Fin.castLE] using congrArg Fin.val hcast
  let H0 : LoopGraph :=
    { vertex := Fin (RamseyNumber s k)
      fintype := inferInstance
      adj := fun i j => H.adj (ι i) (ι j)
      decidableAdj := inferInstance
      symmetric := by intro i j; exact H.symmetric _ _ }
  have hres := hRmem H0 (by simp [H0]) (by
    intro i hi
    exact hloopH (ι i) hi)
  rcases hres with ⟨⟨c⟩⟩ | ⟨⟨c⟩⟩
  · apply hcliqueH
    let v : Fin s → H.vertex := fun i => ι (c.vertex i)
    have hv : Function.Injective v := by
      intro i j hij
      apply c.injective
      exact hι hij
    have ha : ∀ ⦃i j : Fin s⦄, i ≠ j → H.adj (v i) (v j) := by
      intro i j hij
      simpa [v, H0] using c.adjacent hij
    exact ⟨{ vertex := v, injective := hv, adjacent := ha }⟩
  · apply hindH
    let v : Fin k → H.vertex := fun i => ι (c.vertex i)
    have hv : Function.Injective v := by
      intro i j hij
      apply c.injective
      exact hι hij
    have hi : ∀ ⦃i j : Fin k⦄, i ≠ j → ¬ H.adj (v i) (v j) := by
      intro i j hij
      simpa [v, H0] using c.independent hij
    exact ⟨{ vertex := v, injective := hv, independent := hi }⟩
