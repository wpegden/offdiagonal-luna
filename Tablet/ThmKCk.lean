import Tablet.F2ForwardIndependentBound
import Tablet.RandomPermutationReduction
import Tablet.SamplingDeletion

set_option maxHeartbeats 2000000

-- [TABLET NODE: ThmKCk]
theorem ThmKCk :
    ∀ C : ℝ, 1 < C → ∃ S : Nat, ∀ s : Nat, S ≤ s →
      (RamseyNumber s (Nat.ceil (C * (s : ℝ))) : ℝ) ≥
        Real.rpow 2 ((1 - 1 / (2 * C)) * (s : ℝ)) := by
-- BODY
  intro C hC
  obtain ⟨N, hN⟩ := exists_nat_gt (max C (32 * Real.exp 1))
  let S : Nat := max 5 N
  refine ⟨S, ?_⟩
  intro s hsS
  have hs5 : 5 ≤ s := le_trans (le_max_left _ _) hsS
  have hs4 : 4 ≤ s := by omega
  have hNs : N ≤ s := le_trans (le_max_right _ _) hsS
  let k : Nat := Nat.ceil (C * (s : ℝ))
  have hCspos : 0 < C * (s : ℝ) := by positivity
  have hks : s ≤ k := by
    have hceil : C * (s : ℝ) ≤ (k : ℝ) := by
      dsimp [k]
      exact Nat.le_ceil _
    have hCs : (s : ℝ) ≤ C * (s : ℝ) := by
      have hsreal : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
      nlinarith
    exact_mod_cast hCs.trans hceil
  have hkpos : 0 < k := by omega
  have hkceil : (k : ℝ) < C * (s : ℝ) + 1 := by
    dsimp [k]
    exact Nat.ceil_lt_add_one hCspos.le
  have hN32 : 32 * Real.exp 1 < (N : ℝ) :=
    (le_max_right C (32 * Real.exp 1)).trans_lt hN
  have hCsN : C < (N : ℝ) :=
    (le_max_left C (32 * Real.exp 1)).trans_lt hN
  have hCs : C ≤ (s : ℝ) := by
    have hNsR : (N : ℝ) ≤ (s : ℝ) := by exact_mod_cast hNs
    linarith
  have hkupper_real : (k : ℝ) < (s : ℝ) * (s : ℝ) + 1 := by
    calc
      (k : ℝ) < C * (s : ℝ) + 1 := hkceil
      _ ≤ (s : ℝ) * (s : ℝ) + 1 := by
        gcongr
  have hkupper : k ≤ s * s + 1 := by
    exact_mod_cast (le_of_lt hkupper_real)
  have hsquare : ∀ n : Nat, 5 ≤ n → n * n + 1 ≤ 2 ^ n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
        rw [Nat.pow_succ]
        have hnpoly : (n + 1) * (n + 1) + 1 ≤ 2 * (n * n + 1) := by
          nlinarith
        exact hnpoly.trans (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left 2 ih)
  have hkpow : k ≤ 2 ^ s := hkupper.trans (hsquare s hs5)

  have hres : ∀ t : Nat, t ∈ Finset.Icc 1 (s - 1) →
      2 * ((s - 1) * t - Nat.choose (t + 1) 2) ≤ s * s := by
    intro t ht
    have ht' := Finset.mem_Icc.mp ht
    have hchoose : Nat.choose (t + 1) 2 = (t + 1) * t / 2 := by
      simpa [Nat.choose_two_right, Nat.mul_comm]
    rw [hchoose]
    let u : Nat := s - 1 - t
    have hsu : s = t + u + 1 := by
      dsimp [u]
      omega
    have hdivlow : (t + 1) * t ≤ 2 * ((t + 1) * t / 2) + 1 := by
      omega
    have hpoly : 2 * ((s - 1) * t) + 1 ≤ s * s + (t + 1) * t := by
      rw [hsu]
      simp only [Nat.add_sub_cancel]
      nlinarith [Nat.zero_le u]
    have hnonneg : 0 ≤ (s - 1) * t - (t + 1) * t / 2 := by omega
    rw [Nat.mul_sub_left_distrib]
    omega

  have hsum :
      (∑ t ∈ Finset.Icc 1 (s - 1),
        (Nat.choose k t *
          2 ^ ((s - 1) * (t + k) - Nat.choose (t + 1) 2) : Nat) : ℝ) ≤
        Real.rpow 2 ((s * k : ℝ) + (s : ℝ)^2 / 2) := by
    let B : Nat := s * s / 2
    have hterm : ∀ t ∈ Finset.Icc 1 (s - 1),
        Nat.choose k t * 2 ^ ((s - 1) * (t + k) - Nat.choose (t + 1) 2) ≤
          Nat.choose k t * 2 ^ ((s - 1) * k + B) := by
      intro t ht
      have ht' := Finset.mem_Icc.mp ht
      have hchle : Nat.choose (t + 1) 2 ≤ (s - 1) * t := by
        have hchoose : Nat.choose (t + 1) 2 = (t + 1) * t / 2 := by
          simpa [Nat.choose_two_right, Nat.mul_comm]
        rw [hchoose]
        apply (Nat.div_le_iff_le_mul (by omega : 0 < 2)).2
        have hmul : (t + 1) * t ≤ 2 * ((s - 1) * t) := by
          have hh : t + 1 ≤ 2 * (s - 1) := by omega
          exact (Nat.mul_le_mul_right t hh) |>.trans_eq (by ring)
        omega
      have hsplit :
          (s - 1) * (t + k) - Nat.choose (t + 1) 2 =
            (s - 1) * k + ((s - 1) * t - Nat.choose (t + 1) 2) := by
        have hchoose : Nat.choose (t + 1) 2 = (t + 1) * t / 2 := by
          simpa [Nat.choose_two_right, Nat.mul_comm]
        rw [hchoose]
        calc
          (s - 1) * (t + k) - (t + 1) * t / 2 =
              ((s - 1) * t + (s - 1) * k) - (t + 1) * t / 2 := by
                congr 1
                ring
          _ = (s - 1) * k + ((s - 1) * t - (t + 1) * t / 2) := by
                omega
      have hres' := hres t ht
      have hhalf : (s - 1) * t - Nat.choose (t + 1) 2 ≤ B := by
        dsimp [B]
        apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
        simpa [Nat.mul_comm] using hres'
      rw [hsplit]
      have hp := Nat.pow_le_pow_right (by omega : 0 < 2)
        (Nat.add_le_add_left hhalf ((s - 1) * k))
      exact Nat.mul_le_mul_left _ hp
    have hsumterm :
        (∑ t ∈ Finset.Icc 1 (s - 1),
          Nat.choose k t * 2 ^ ((s - 1) * (t + k) - Nat.choose (t + 1) 2)) ≤
          (∑ t ∈ Finset.Icc 1 (s - 1), Nat.choose k t) *
            2 ^ ((s - 1) * k + B) := by
      calc
        _ ≤ ∑ t ∈ Finset.Icc 1 (s - 1),
            Nat.choose k t * 2 ^ ((s - 1) * k + B) := by
              apply Finset.sum_le_sum
              intro t ht
              exact hterm t ht
        _ = _ := by rw [Finset.sum_mul]
    have hsub : Finset.Icc 1 (s - 1) ⊆ Finset.range (k + 1) := by
      intro t ht
      have ht' := Finset.mem_Icc.mp ht
      simp only [Finset.mem_range]
      omega
    have hchoose_sum :
        (∑ t ∈ Finset.Icc 1 (s - 1), Nat.choose k t) ≤ 2 ^ k := by
      calc
        _ ≤ ∑ t ∈ Finset.range (k + 1), Nat.choose k t := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro t ht hnot
          positivity
        _ = 2 ^ k := by simpa using Nat.sum_range_choose k
    have hnat :
        (∑ t ∈ Finset.Icc 1 (s - 1),
          Nat.choose k t * 2 ^ ((s - 1) * (t + k) - Nat.choose (t + 1) 2)) ≤
          2 ^ (s * k + s * s / 2) := by
      calc
        _ ≤ (2 ^ k) * 2 ^ ((s - 1) * k + B) :=
          hsumterm.trans (Nat.mul_le_mul_right _ hchoose_sum)
        _ = 2 ^ (k + ((s - 1) * k + B)) := by rw [← pow_add]
        _ = 2 ^ (s * k + s * s / 2) := by
          congr 1
          have hmul : k + (s - 1) * k = s * k := by
            calc
              k + (s - 1) * k = (s - 1) * k + k := by omega
              _ = ((s - 1) + 1) * k := by rw [Nat.add_mul]; omega
              _ = s * k := by congr 1 <;> omega
          dsimp [B]
          rw [← Nat.add_assoc, hmul]
    have hB : (B : ℝ) ≤ (s : ℝ)^2 / 2 := by
      dsimp [B]
      calc
        ((s * s / 2 : Nat) : ℝ) ≤ ((s * s : Nat) : ℝ) / 2 := by
          exact Nat.cast_div_le
        _ = (s : ℝ)^2 / 2 := by norm_num [Nat.cast_mul]; ring
    have hEreal : ((s * k + s * s / 2 : Nat) : ℝ) ≤
        (s * k : ℝ) + (s : ℝ)^2 / 2 := by
      have hB' : ((s * s / 2 : Nat) : ℝ) ≤ (s : ℝ)^2 / 2 := by
        simpa [B] using hB
      calc
        ((s * k + s * s / 2 : Nat) : ℝ) =
            (s * k : ℝ) + ((s * s / 2 : Nat) : ℝ) := by
              norm_num [Nat.cast_add]
        _ ≤ (s * k : ℝ) + (s : ℝ)^2 / 2 := by
          simpa [add_comm] using add_le_add_left hB' (s * k : ℝ)
    have hcast :
        ((2 ^ (s * k + s * s / 2) : Nat) : ℝ) ≤
          Real.rpow 2 ((s * k : ℝ) + (s : ℝ)^2 / 2) := by
      calc
        ((2 ^ (s * k + s * s / 2) : Nat) : ℝ) =
            Real.rpow 2 ((s * k + s * s / 2 : Nat) : ℝ) := by
              calc
                ((2 ^ (s * k + s * s / 2) : Nat) : ℝ) =
                    (2 : ℝ) ^ (s * k + s * s / 2) := by
                      norm_num [Nat.cast_pow]
                _ = Real.rpow 2 ((s * k + s * s / 2 : Nat) : ℝ) :=
                  (Real.rpow_natCast 2 _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hEreal
    have hnatR :
        (∑ t ∈ Finset.Icc 1 (s - 1),
          (Nat.choose k t *
            2 ^ ((s - 1) * (t + k) - Nat.choose (t + 1) 2) : Nat) : ℝ) ≤
          ((2 ^ (s * k + s * s / 2) : Nat) : ℝ) := by
      exact_mod_cast hnat
    exact hnatR.trans hcast

  obtain ⟨D, hD, hDfree, hDcard, hDfwi⟩ :=
    F2ForwardIndependentBound s k hs4 hks
  obtain ⟨G, hGcard, hGloop, hGfree, hGind⟩ :=
    RandomPermutationReduction D s k hDfree hkpos
  have hIupper : (IndependentSetCount G k : ℝ) ≤
      (Real.exp 1 / (k : ℝ)) ^ k *
        Real.rpow 2 ((s * k : ℝ) + (s : ℝ)^2 / 2) := by
    calc
      (IndependentSetCount G k : ℝ) ≤
          (Real.exp 1 / (k : ℝ)) ^ k *
            (ForwardIndependentCount D k : ℝ) := hGind
      _ ≤ (Real.exp 1 / (k : ℝ)) ^ k *
          (∑ t ∈ Finset.Icc 1 (s - 1),
            (Nat.choose k t *
              2 ^ ((s - 1) * (t + k) - Nat.choose (t + 1) 2) : Nat) : ℝ) := by
            gcongr
      _ ≤ _ := by gcongr
  let E : ℝ := (s : ℝ) + (s : ℝ)^2 / (2 * (k : ℝ))
  let p : ℝ := (k : ℝ) / Real.exp 1 * Real.rpow 2 (-E)
  have hEident : E * (k : ℝ) =
      (s * k : ℝ) + (s : ℝ)^2 / 2 := by
    dsimp [E]
    field_simp
  have hroot : (Real.rpow 2 (-E)) ^ k =
      Real.rpow 2 (-E * (k : ℝ)) := by
    calc
      (Real.rpow 2 (-E)) ^ k =
          Real.rpow (Real.rpow 2 (-E)) (k : ℝ) :=
        (Real.rpow_natCast _ _).symm
      _ = Real.rpow 2 (-E * (k : ℝ)) := by
        exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)
          (-E) (k : ℝ)).symm
  have hrat : ((k : ℝ) / Real.exp 1) ^ k *
      (Real.exp 1 / (k : ℝ)) ^ k = 1 := by
    rw [← mul_pow]
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hkpos)
    field_simp [hk0, Real.exp_ne_zero]
    simp
  have hpowcancel : Real.rpow 2 (-E * (k : ℝ)) *
      Real.rpow 2 ((s * k : ℝ) + (s : ℝ)^2 / 2) = 1 := by
    calc
      Real.rpow 2 (-E * (k : ℝ)) *
          Real.rpow 2 ((s * k : ℝ) + (s : ℝ)^2 / 2) =
          Real.rpow 2 (-E * (k : ℝ) +
            ((s * k : ℝ) + (s : ℝ)^2 / 2)) :=
        (Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _).symm
      _ = 1 := by
        rw [show -E * (k : ℝ) + ((s * k : ℝ) + (s : ℝ)^2 / 2) = 0 by
          rw [← hEident]
          ring]
        simp
  have hp0 : 0 ≤ p := by
    dsimp [p]
    positivity
  have hcount : p ^ k * (IndependentSetCount G k : ℝ) ≤ 1 := by
    calc
      p ^ k * (IndependentSetCount G k : ℝ) ≤
          p ^ k * ((Real.exp 1 / (k : ℝ)) ^ k *
            Real.rpow 2 ((s * k : ℝ) + (s : ℝ)^2 / 2)) := by
              gcongr
      _ = 1 := by
        dsimp [p]
        change (((k : ℝ) / Real.exp 1 * Real.rpow 2 (-E)) ^ k) *
          ((Real.exp 1 / (k : ℝ)) ^ k *
            Real.rpow 2 ((s * k : ℝ) + (s : ℝ)^2 / 2)) = 1
        rw [mul_pow]
        rw [hroot]
        calc
          ((k : ℝ) / Real.exp 1) ^ k * Real.rpow 2 (-E * (k : ℝ)) *
              ((Real.exp 1 / (k : ℝ)) ^ k *
                Real.rpow 2 ((s * k : ℝ) + (s : ℝ)^2 / 2)) =
              (((k : ℝ) / Real.exp 1) ^ k *
                (Real.exp 1 / (k : ℝ)) ^ k) *
                (Real.rpow 2 (-E * (k : ℝ)) *
                  Real.rpow 2 ((s * k : ℝ) + (s : ℝ)^2 / 2)) := by ring
          _ = 1 := by rw [hrat, hpowcancel]; ring
  have hEge : (s : ℝ) ≤ E := by
    dsimp [E]
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
    have hsR : (0 : ℝ) ≤ (s : ℝ) := by positivity
    have hnonneg : 0 ≤ (s : ℝ)^2 / (2 * (k : ℝ)) := by positivity
    linarith
  have hpowneg : Real.rpow 2 (-E) ≤ Real.rpow 2 (-(s : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hexp1 : (1 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    norm_num at h ⊢
  have hkdivexp : (k : ℝ) / Real.exp 1 ≤ (k : ℝ) := by
    apply (div_le_iff₀ (Real.exp_pos 1)).2
    nlinarith [show (0 : ℝ) ≤ (k : ℝ) by positivity]
  have hkpowR : (k : ℝ) ≤ (2 : ℝ)^s := by exact_mod_cast hkpow
  have hknpow : (k : ℝ) * Real.rpow 2 (-(s : ℝ)) ≤ 1 := by
    have hpowcast : Real.rpow 2 (-(s : ℝ)) = ((2 : ℝ)^s)⁻¹ := by
      calc
        Real.rpow 2 (-(s : ℝ)) = (Real.rpow 2 (s : ℝ))⁻¹ :=
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) _
        _ = ((2 : ℝ)^s)⁻¹ := by
          congr 1
          exact Real.rpow_natCast _ _
    rw [hpowcast]
    have hdiv : (k : ℝ) / (2 : ℝ)^s ≤ 1 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ)^s)).2
      simpa using hkpowR
    simpa [div_eq_mul_inv] using hdiv
  have hp1 : p ≤ 1 := by
    calc
      p ≤ (k : ℝ) / Real.exp 1 * Real.rpow 2 (-(s : ℝ)) := by
        dsimp [p]
        exact mul_le_mul_of_nonneg_left hpowneg (by positivity)
      _ ≤ (k : ℝ) * Real.rpow 2 (-(s : ℝ)) :=
        mul_le_mul_of_nonneg_right hkdivexp
          (Real.rpow_nonneg (by norm_num) _)
      _ ≤ 1 := hknpow
  have hcardnat : 2 ^ (2 * s - 4) ≤ 2 ^ (2 * s - 3) - 2 ^ (s - 2) := by
    have hexp : 2 * s - 3 = (2 * s - 4) + 1 := by omega
    have he : s - 2 ≤ 2 * s - 4 := by omega
    have hy : 2 ^ (s - 2) ≤ 2 ^ (2 * s - 4) :=
      Nat.pow_le_pow_right (by omega) he
    rw [hexp, Nat.pow_succ]
    omega
  have hcardlower :
      ((2 ^ (2 * s - 4) : Nat) : ℝ) ≤
        (@Fintype.card G.vertex G.fintype : ℝ) := by
    have hDlower : 2 ^ (2 * s - 4) ≤
        @Fintype.card D.vertex D.fintype := by
      rw [hDcard]
      exact hcardnat
    have hGlower : 2 ^ (2 * s - 4) ≤
        @Fintype.card G.vertex G.fintype := hDlower.trans_eq hGcard.symm
    exact_mod_cast hGlower
  have hcardpow : (2 : ℝ)^(2 * s - 4) ≤
      (@Fintype.card G.vertex G.fintype : ℝ) := by
    calc
      (2 : ℝ)^(2 * s - 4) = ((2 ^ (2 * s - 4) : Nat) : ℝ) := by
        norm_num [Nat.cast_pow]
      _ ≤ _ := hcardlower
  let T : ℝ := (1 - 1 / (2 * C)) * (s : ℝ)
  have hCpos : 0 < C := by linarith
  have hcoefpos : 0 < 1 - 1 / (2 * C) := by
    have hden : (1 : ℝ) < 2 * C := by nlinarith
    have hi : 1 / (2 * C) < 1 := by
      apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * C)).2
      linarith
    linarith
  have hTnonneg : 0 ≤ T := by
    dsimp [T]
    positivity
  have hTleS : T ≤ (s : ℝ) := by
    dsimp [T]
    have hi : 0 ≤ 1 / (2 * C) := by positivity
    nlinarith
  have hpowTle : Real.rpow 2 T ≤ (2 : ℝ)^s := by
    calc
      Real.rpow 2 T ≤ Real.rpow 2 (s : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hTleS
      _ = (2 : ℝ)^s := Real.rpow_natCast _ _
  have hpowgap : (2 : ℝ)^s + 1 ≤ (2 : ℝ)^(2 * s - 4) := by
    have hpow_succ : (2 : ℝ)^s + 1 ≤ (2 : ℝ)^(s + 1) := by
      calc
        (2 : ℝ)^s + 1 ≤ (2 : ℝ)^s + (2 : ℝ)^s := by
          have h1 : (1 : ℝ) ≤ (2 : ℝ)^s := one_le_pow₀ (by norm_num)
          linarith
        _ = (2 : ℝ)^(s + 1) := by rw [pow_succ]; ring
    have hexp : s + 1 ≤ 2 * s - 4 := by omega
    exact hpow_succ.trans (by
      apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      exact hexp)
  have hzero_card : Real.rpow 2 T + 1 ≤
      (@Fintype.card G.vertex G.fintype : ℝ) := by
    have hadd : Real.rpow 2 T + 1 ≤ (2 : ℝ)^s + 1 :=
      by simpa [add_comm] using add_le_add_right hpowTle 1
    exact hadd.trans (hpowgap.trans hcardpow)
  have hksreal : C * (s : ℝ) ≤ (k : ℝ) := by
    dsimp [k]
    exact Nat.le_ceil _
  have hquad : (s : ℝ)^2 / (2 * (k : ℝ)) ≤
      (s : ℝ) / (2 * C) := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (k : ℝ))
      (by positivity : (0 : ℝ) < 2 * C)).2
    have hh := mul_le_mul_of_nonneg_left hksreal
      (show (0 : ℝ) ≤ (s : ℝ) by positivity)
    nlinarith
  have hPbound : T - 4 ≤ -E + ((2 * s - 4 : Nat) : ℝ) := by
    have hcast : ((2 * s - 4 : Nat) : ℝ) = 2 * (s : ℝ) - 4 := by
      rw [Nat.cast_sub (by omega : 4 ≤ 2 * s)]
      push_cast
      ring
    have hh : (s : ℝ) - (s : ℝ) / (2 * C) - 4 ≤
        (s : ℝ) - (s : ℝ)^2 / (2 * (k : ℝ)) - 4 := by
      linarith [hquad]
    dsimp [T]
    rw [hcast]
    dsimp [E]
    convert hh using 1 <;> ring
  have hpowlower : Real.rpow 2 (T - 4) ≤
      Real.rpow 2 (-E + ((2 * s - 4 : Nat) : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hPbound
  have hshift : 2 * Real.rpow 2 T ≤
      32 * Real.rpow 2 (-E + ((2 * s - 4 : Nat) : ℝ)) := by
    have hpow4 : Real.rpow 2 (4 : ℝ) = 16 := by
      norm_num [Real.rpow_natCast]
    have hid : 2 * Real.rpow 2 T = 32 * Real.rpow 2 (T - 4) := by
      calc
        2 * Real.rpow 2 T =
            2 * (Real.rpow 2 (T - 4) * Real.rpow 2 (4 : ℝ)) := by
              congr 2
              calc
                Real.rpow 2 T =
                    Real.rpow 2 ((T - 4) + 4) := by congr 1 <;> ring
                _ = Real.rpow 2 (T - 4) * Real.rpow 2 (4 : ℝ) :=
                  Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _
        _ = 32 * Real.rpow 2 (T - 4) := by rw [hpow4]; ring
    calc
      2 * Real.rpow 2 T = 32 * Real.rpow 2 (T - 4) := hid
      _ ≤ 32 * Real.rpow 2 (-E + ((2 * s - 4 : Nat) : ℝ)) :=
        mul_le_mul_of_nonneg_left hpowlower (by norm_num)
  have hk32 : 32 * Real.exp 1 < (k : ℝ) := by
    have hNsR : (N : ℝ) ≤ (s : ℝ) := by exact_mod_cast hNs
    have hskR : (s : ℝ) ≤ (k : ℝ) := by exact_mod_cast hks
    exact hN32.trans_le (hNsR.trans hskR)
  have hke32 : (32 : ℝ) ≤ (k : ℝ) / Real.exp 1 := by
    apply (le_div_iff₀ (Real.exp_pos 1)).2
    exact le_of_lt hk32
  have hfactor : 2 * Real.rpow 2 T ≤
      (k : ℝ) / Real.exp 1 *
        Real.rpow 2 (-E + ((2 * s - 4 : Nat) : ℝ)) := by
    exact hshift.trans (mul_le_mul_of_nonneg_right hke32
      (Real.rpow_nonneg (by norm_num) _))
  have hcombine : p * (2 : ℝ)^(2 * s - 4) =
      (k : ℝ) / Real.exp 1 *
        Real.rpow 2 (-E + ((2 * s - 4 : Nat) : ℝ)) := by
    dsimp [p]
    calc
      (k : ℝ) / Real.exp 1 * Real.rpow 2 (-E) *
          (2 : ℝ)^(2 * s - 4) =
          (k : ℝ) / Real.exp 1 *
            (Real.rpow 2 (-E) *
              Real.rpow 2 ((2 * s - 4 : Nat) : ℝ)) := by
                have hh : (2 : ℝ)^(2 * s - 4) =
                    Real.rpow 2 ((2 * s - 4 : Nat) : ℝ) :=
                  (Real.rpow_natCast _ _).symm
                calc
                  (k : ℝ) / Real.exp 1 * Real.rpow 2 (-E) *
                      (2 : ℝ)^(2 * s - 4) =
                      (k : ℝ) / Real.exp 1 * Real.rpow 2 (-E) *
                        Real.rpow 2 ((2 * s - 4 : Nat) : ℝ) := by rw [hh]
                  _ = (k : ℝ) / Real.exp 1 *
                      (Real.rpow 2 (-E) *
                        Real.rpow 2 ((2 * s - 4 : Nat) : ℝ)) := by ring
      _ = (k : ℝ) / Real.exp 1 *
          Real.rpow 2 (-E + ((2 * s - 4 : Nat) : ℝ)) := by
            congr 1
            exact (Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _).symm
  have hpcard : 2 * Real.rpow 2 T ≤
      p * (@Fintype.card G.vertex G.fintype : ℝ) := by
    calc
      2 * Real.rpow 2 T ≤
          (k : ℝ) / Real.exp 1 *
            Real.rpow 2 (-E + ((2 * s - 4 : Nat) : ℝ)) := hfactor
      _ = p * (2 : ℝ)^(2 * s - 4) := hcombine.symm
      _ ≤ p * (@Fintype.card G.vertex G.fintype : ℝ) :=
        mul_le_mul_of_nonneg_left hcardpow hp0
  by_cases hIzero : IndependentSetCount G k = 0
  · have hsamp := SamplingDeletion G s k hGloop hGfree hkpos
      1 (by norm_num) (by norm_num) (by simp [hIzero])
    have hR : (RamseyNumber s k : ℝ) >
        (@Fintype.card G.vertex G.fintype : ℝ) - 1 := by
      simpa using hsamp
    have hTcard : Real.rpow 2 T ≤
        (@Fintype.card G.vertex G.fintype : ℝ) - 1 := by linarith
    have hRle : Real.rpow 2 T ≤ (RamseyNumber s k : ℝ) :=
      hTcard.trans (le_of_lt hR)
    simpa [k, T] using hRle
  · have hsamp := SamplingDeletion G s k hGloop hGfree hkpos
      p hp0 hp1 hcount
    have hR : (RamseyNumber s k : ℝ) >
        p * (@Fintype.card G.vertex G.fintype : ℝ) - 1 := by
      simpa using hsamp
    have hTone : (1 : ℝ) ≤ Real.rpow 2 T := by
      calc
        (1 : ℝ) = Real.rpow 2 0 := by norm_num
        _ ≤ Real.rpow 2 T :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hTnonneg
    have hRle : Real.rpow 2 T ≤ (RamseyNumber s k : ℝ) := by
      linarith [hpcard, hTone]
    simpa [k, T] using hRle
