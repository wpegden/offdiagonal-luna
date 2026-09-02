import Tablet.F2RankSequenceBound

open scoped BigOperators

set_option maxHeartbeats 2000000

-- [TABLET NODE: F2AsymptoticCorollary]
theorem F2AsymptoticCorollary :
    ∀ (s a : Nat → Nat), Filter.Tendsto s Filter.atTop Filter.atTop →
      (fun n => (a n : ℝ)) =o[Filter.atTop] (fun n => (s n : ℝ)) →
      ∃ e : Nat → ℝ,
        (fun n => e n) =o[Filter.atTop] (fun n => (s n : ℝ)) ∧
        ∀ᶠ n in Filter.atTop,
          (∑ t ∈ Finset.Icc 1 (s n - 1),
            (Nat.choose (s n + a n) t *
              2 ^ ((s n - 1) * (t + (s n + a n)) -
                Nat.choose (t + 1) 2) : Nat) : ℝ) ≤
            Real.rpow 2
              (3 / 2 * (s n : ℝ) ^ 2 +
                (a n : ℝ) * (s n : ℝ) - 5 / 2 * (s n : ℝ) + e n) := by
-- BODY
  intro s a hs ha
  have hfactorial : ∀ n : Nat, ((n : ℝ) / 8) ^ n ≤ (Nat.factorial n : ℝ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        rcases n with _ | n
        · simp
        by_cases hev : Even (n + 1)
        · obtain ⟨m, hm⟩ := hev
          have hmn : m < n + 1 := by omega
          have hih := ih m hmn
          have hfac := Nat.factorial_mul_pow_le_factorial (m := m) (n := m)
          rw [← hm] at hfac
          have hfac' : ((Nat.factorial m : ℝ) * (m + 1) ^ m) ≤
              (Nat.factorial (n + 1) : ℝ) := by exact_mod_cast hfac
          have hbase : (((n + 1 : ℕ) : ℝ) / 8) ^ (n + 1) ≤
              ((m : ℝ) / 8) ^ m * (m + 1) ^ m := by
            rw [hm, Nat.cast_add, add_div, pow_add]
            conv_lhs => rw [← mul_pow]
            conv_rhs => rw [← mul_pow]
            apply pow_le_pow_left₀ (M₀ := ℝ) (by positivity) ?_ m
            have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
            nlinarith
          calc
            (((n + 1 : ℕ) : ℝ) / 8) ^ (n + 1) ≤
                ((m : ℝ) / 8) ^ m * (m + 1) ^ m := hbase
            _ ≤ (Nat.factorial m : ℝ) * (m + 1) ^ m := by gcongr
            _ ≤ (Nat.factorial (n + 1) : ℝ) := hfac'
        · have hodd : Odd (n + 1) := (Nat.not_even_iff_odd.mp hev)
          obtain ⟨m, hm⟩ := hodd
          have hmn : m < n + 1 := by omega
          have hih := ih m hmn
          have hfac : m.factorial * (m + 1) ^ (m + 1) ≤ (n + 1).factorial := by
            have hfac0 := Nat.factorial_mul_pow_le_factorial (m := m) (n := m + 1)
            have heq : m + (m + 1) = n + 1 := by omega
            rw [heq] at hfac0
            exact hfac0
          have hfac' : ((Nat.factorial m : ℝ) * (m + 1) ^ (m + 1)) ≤
              (Nat.factorial (n + 1) : ℝ) := by exact_mod_cast hfac
          have hbase : (((n + 1 : ℕ) : ℝ) / 8) ^ (n + 1) ≤
              ((m : ℝ) / 8) ^ m * (m + 1) ^ (m + 1) := by
            rw [hm, Nat.cast_add, Nat.cast_one]
            by_cases hm0 : m = 0
            · subst m
              norm_num
            · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
              have hmpos' : (0 : ℝ) < m := Nat.cast_pos.mpr hmpos
              have hm1 : (1 : ℝ) ≤ m := by
                exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm0)
              let x : ℝ := (2 * (m : ℝ) + 1) / 8
              let y : ℝ := (m : ℝ) / 8
              have hratio : x ^ 2 ≤ y * (m + 1) := by
                dsimp [x, y]
                norm_num [div_pow]
                field_simp
                nlinarith [sq_nonneg (2 * (m : ℝ) - 1)]
              have hxy : x ≤ m + 1 := by
                dsimp [x]
                nlinarith
              have hcalc : x ^ (2 * m + 1) ≤ y ^ m * (m + 1) ^ (m + 1) := by
                calc
                  x ^ (2 * m + 1) = (x ^ 2) ^ m * x := by
                    rw [pow_add, ← pow_mul, pow_one]
                  _ ≤ (y * (m + 1)) ^ m * (m + 1) := by gcongr
                  _ = y ^ m * (m + 1) ^ (m + 1) := by rw [mul_pow, pow_succ]; ring
              simpa [x, y, Nat.cast_add, Nat.cast_one] using hcalc
          calc
            (((n + 1 : ℕ) : ℝ) / 8) ^ (n + 1) ≤
                ((m : ℝ) / 8) ^ m * (m + 1) ^ (m + 1) := hbase
            _ ≤ (Nat.factorial m : ℝ) * (m + 1) ^ (m + 1) := by gcongr
            _ ≤ (Nat.factorial (n + 1) : ℝ) := hfac'
  have hpow_log {x : ℝ} (hx : 0 < x) (m : Nat) :
      x ^ m = Real.rpow 2 ((m : ℝ) * (Real.log x / Real.log 2)) := by
    change x ^ m = (2 : ℝ) ^ ((m : ℝ) * (Real.log x / Real.log 2))
    calc
      x ^ m = Real.rpow x (m : ℝ) := (Real.rpow_natCast x m).symm
      _ = Real.exp (Real.log x * (m : ℝ)) := Real.rpow_def_of_pos hx _
      _ = Real.exp (Real.log 2 * ((m : ℝ) * (Real.log x / Real.log 2))) := by
        congr 1
        field_simp
      _ = Real.rpow 2 ((m : ℝ) * (Real.log x / Real.log 2)) :=
        (Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) _).symm
  have hsqrt_littleo (u : Nat → Nat) (hu : Filter.Tendsto u Filter.atTop Filter.atTop) :
      (fun n => Real.sqrt (u n : ℝ)) =o[Filter.atTop] (fun n => (u n : ℝ)) := by
    apply Asymptotics.IsLittleO.of_bound
    intro c hc
    have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
    obtain ⟨N, hN⟩ := exists_nat_gt ((c⁻¹) ^ 2)
    filter_upwards [hu.eventually_ge_atTop N] with n hn
    have hu0 : 0 ≤ (u n : ℝ) := Nat.cast_nonneg _
    have hnR : (c⁻¹) ^ 2 ≤ (u n : ℝ) :=
      le_trans (le_of_lt hN) (Nat.cast_le.mpr hn)
    have h1 : 1 ≤ c ^ 2 * (u n : ℝ) := by
      calc
        1 = c ^ 2 * (c⁻¹) ^ 2 := by field_simp
        _ ≤ c ^ 2 * (u n : ℝ) := by gcongr
    have hsq : (u n : ℝ) ≤ (c * (u n : ℝ)) ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_right h1 hu0
      nlinarith
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [abs_of_nonneg hu0, Real.sqrt_le_left (by positivity : 0 ≤ c * (u n : ℝ))]
    exact hsq
  have hprod_littleo :
      (fun n => Real.sqrt ((a n : ℝ) * (s n : ℝ))) =o[Filter.atTop]
        (fun n => (s n : ℝ)) := by
    apply Asymptotics.IsLittleO.of_bound
    intro c hc
    have hc2 : 0 < c ^ (2 : Nat) := by positivity
    filter_upwards [ha.def hc2, hs.eventually_gt_atTop 0] with n hna hsn
    have ha0 : (0 : ℝ) ≤ (a n : ℝ) := Nat.cast_nonneg _
    have hs0 : (0 : ℝ) ≤ (s n : ℝ) := Nat.cast_nonneg _
    have hna' : (a n : ℝ) ≤ c ^ 2 * (s n : ℝ) := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg ha0, abs_of_nonneg hs0] using hna
    have hmul := mul_le_mul_of_nonneg_right hna' hs0
    have hsq : (a n : ℝ) * (s n : ℝ) ≤ (c * (s n : ℝ)) ^ 2 := by
      nlinarith
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [abs_of_nonneg hs0, Real.sqrt_le_left (by positivity : 0 ≤ c * (s n : ℝ))]
    exact hsq
  have hsqrt_ratio {A S X : ℝ} (hA : 0 < A) (hAS : A ≤ S)
    (hX : X ≤ 16 * S / A) (hX0 : 0 ≤ X) :
    A * Real.sqrt X ≤ 4 * Real.sqrt (A * S) := by  
    have hA0 : 0 ≤ A := le_of_lt hA
    have hAX : X * A ≤ 16 * S := by
      exact (le_div_iff₀ hA).mp hX
    have hA2X : A * (X * A) ≤ A * (16 * S) :=
      mul_le_mul_of_nonneg_left hAX hA0
    have hsq : (A * Real.sqrt X) ^ 2 ≤ (4 * Real.sqrt (A * S)) ^ 2 := by
      simp only [mul_pow, Real.sq_sqrt hX0,
        Real.sq_sqrt (mul_nonneg hA0 (hA0.trans hAS))]
      nlinarith
    have hl : 0 ≤ A * Real.sqrt X := mul_nonneg hA0 (Real.sqrt_nonneg _)
    have hr : 0 ≤ 4 * Real.sqrt (A * S) := by positivity
    nlinarith
  
  have hchoose_split (k a j : Nat) (ha : 1 ≤ a) :
    (Nat.choose k (a + j) : ℝ) ≤
      (8 * (k : ℝ) / (a : ℝ)) ^ a * (k : ℝ) ^ j := by  
    have hdiv := Nat.choose_le_pow_div (α := ℝ) (a + j) k
    have hdiv' : (Nat.choose k (a + j) : ℝ) ≤
        (k : ℝ) ^ (a + j) / (Nat.factorial (a + j) : ℝ) := by
      exact_mod_cast hdiv
    have hfact : (Nat.factorial a : ℝ) ≤ (Nat.factorial (a + j) : ℝ) := by
      exact_mod_cast Nat.factorial_le (Nat.le_add_right a j)
    have hfactpos : 0 < (Nat.factorial a : ℝ) := by positivity
    have hdiv2 : (k : ℝ) ^ (a + j) / (Nat.factorial (a + j) : ℝ) ≤
        (k : ℝ) ^ (a + j) / (Nat.factorial a : ℝ) := by
      gcongr
    calc
      (Nat.choose k (a + j) : ℝ) ≤
          (k : ℝ) ^ (a + j) / (Nat.factorial (a + j) : ℝ) := hdiv'
      _ ≤ (k : ℝ) ^ (a + j) / (Nat.factorial a : ℝ) := hdiv2
      _ ≤ (k : ℝ) ^ (a + j) / ((a : ℝ) / 8) ^ a := by
        have hf := hfactorial a
        gcongr
      _ = (8 * (k : ℝ) / (a : ℝ)) ^ a * (k : ℝ) ^ j := by
        have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
        rw [pow_add]
        simp only [div_pow]
        have hcancel : (a : ℝ) ^ a * ((a : ℝ)⁻¹) ^ a = 1 := by
          rw [← mul_pow, mul_inv_cancel₀ ha0, one_pow]
        field_simp [ha0, pow_ne_zero a ha0]
        ring
  
  have hpoint (S A j : Nat) (hS : 2 ≤ S) (hA : A ≤ S)
    (hj : 1 ≤ j) (hjS : j ≤ S - 1) :
    ((Nat.choose (S + A) (S - j) *
      2 ^ ((S - 1) * ((S - j) + (S + A)) -
        Nat.choose ((S - j) + 1) 2) : Nat) : ℝ) ≤
      Real.rpow 2
        (3 / 2 * (S : ℝ) ^ 2 + (A : ℝ) * (S : ℝ) -
          5 / 2 * (S : ℝ) +
          1000 * Real.sqrt ((A : ℝ) * (S : ℝ)) +
          10000 * Real.sqrt (S : ℝ)) := by  
    have hS1 : 1 ≤ S := by omega
    have hjle : j ≤ S := by omega
    have hsum : (S - j) + (A + j) = S + A := by omega
    have hchooseeq : Nat.choose (S + A) (S - j) = Nat.choose (S + A) (A + j) := by
      exact Nat.choose_symm_of_eq_add hsum.symm
    have hE :
        (((S - 1) * ((S - j) + (S + A)) -
          Nat.choose ((S - j) + 1) 2 : ℕ) : ℝ) =
          3 / 2 * (S : ℝ) ^ 2 + (A : ℝ) * (S : ℝ) -
            5 / 2 * (S : ℝ) - (A : ℝ) +
            3 / 2 * (j : ℝ) - 1 / 2 * (j : ℝ) ^ 2 := by
      have hchoose : Nat.choose ((S - j) + 1) 2 ≤
          (S - 1) * ((S - j) + (S + A)) := by
        rw [Nat.choose_two_right]
        have ht : S - j ≤ S - 1 := by omega
        have htk : (S - j) + 1 ≤ (S - j) + (S + A) := by omega
        have hprod : (S - j) * ((S - j) + 1) ≤
            (S - 1) * ((S - j) + (S + A)) := by
          exact Nat.mul_le_mul ht htk
        calc
          ((S - j + 1) * (S - j + 1 - 1)) / 2 ≤
              (S - j + 1) * (S - j + 1 - 1) := Nat.div_le_self _ _
          _ = (S - j) * ((S - j) + 1) := Nat.mul_comm _ _
          _ ≤ (S - 1) * ((S - j) + (S + A)) := hprod
      rw [Nat.cast_sub hchoose]
      push_cast
      have hchoose_two : ∀ n : Nat,
          (Nat.choose (n + 1) 2 : ℝ) = (n : ℝ) * (n + 1) / 2 := by
        intro n
        induction n with
        | zero => norm_num
        | succ n ih =>
            rw [show (2 : Nat) = 1 + 1 by omega, Nat.choose_succ_succ,
              Nat.choose_one_right]
            have ih' : (Nat.choose (n + 1) (Nat.succ 1) : ℝ) =
                (n : ℝ) * (n + 1) / 2 := by simpa using ih
            push_cast
            rw [ih']
            push_cast
            ring
      rw [hchoose_two]
      rw [Nat.cast_sub hjle]
      rw [Nat.cast_sub (by omega : 1 ≤ S)]
      ring
    have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h ⊢
      linarith
    have hlog2_le_sqrt {x : ℝ} (hx : 1 ≤ x) :
        Real.log x / Real.log 2 ≤ 4 * Real.sqrt x := by
      have hx0 : 0 ≤ x := (by norm_num : (0 : ℝ) ≤ 1).trans hx
      have hlog : Real.log x ≤ 2 * Real.sqrt x := by
        have hsx : 1 ≤ Real.sqrt x := by
          apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) hx0).2
          nlinarith
        calc
          Real.log x = 2 * Real.log (Real.sqrt x) := by
            rw [Real.log_sqrt hx0]
            ring
          _ ≤ 2 * (Real.sqrt x - 1) := by
            gcongr
            exact Real.log_le_sub_one_of_pos (by positivity)
          _ ≤ 2 * Real.sqrt x := by nlinarith
      have hlogtwo0 : 0 < Real.log 2 := by linarith
      apply (div_le_iff₀ hlogtwo0).2
      have hmul := mul_le_mul_of_nonneg_right hlogtwo (Real.sqrt_nonneg x)
      nlinarith
    have hlog2_le_fourth {x : ℝ} (hx : 1 ≤ x) :
        Real.log x / Real.log 2 ≤ 8 * Real.sqrt (Real.sqrt x) := by
      have hx0 : 0 ≤ x := (by norm_num : (0 : ℝ) ≤ 1).trans hx
      have hlog : Real.log x ≤ 4 * Real.sqrt (Real.sqrt x) := by
        have hinner : Real.log (Real.sqrt x) ≤
            2 * Real.sqrt (Real.sqrt x) := by
          calc
            Real.log (Real.sqrt x) =
                2 * Real.log (Real.sqrt (Real.sqrt x)) := by
              rw [Real.log_sqrt (Real.sqrt_nonneg x)]
              ring
            _ ≤ 2 * (Real.sqrt (Real.sqrt x) - 1) := by
              gcongr
              exact Real.log_le_sub_one_of_pos (by positivity)
            _ ≤ 2 * Real.sqrt (Real.sqrt x) := by nlinarith
        calc
          Real.log x = 2 * Real.log (Real.sqrt x) := by
            rw [Real.log_sqrt hx0]
            ring
          _ ≤ 4 * Real.sqrt (Real.sqrt x) := by nlinarith
      have hlogtwo0 : 0 < Real.log 2 := by linarith
      apply (div_le_iff₀ hlogtwo0).2
      have hmul := mul_le_mul_of_nonneg_right hlogtwo
        (Real.sqrt_nonneg (Real.sqrt x))
      nlinarith
    have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg _
    have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg _
    have hK0 : (0 : ℝ) ≤ S + A := by positivity
    have hKpos : 0 < (S + A : ℝ) := by positivity
    have hcast :
        ((Nat.choose (S + A) (S - j) *
          2 ^ ((S - 1) * ((S - j) + (S + A)) -
            Nat.choose ((S - j) + 1) 2) : Nat) : ℝ) =
          (Nat.choose (S + A) (S - j) : ℝ) *
            Real.rpow 2 (((S - 1) * ((S - j) + (S + A)) -
              Nat.choose ((S - j) + 1) 2 : Nat) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_pow]
      congr 1
      exact (Real.rpow_natCast (2 : ℝ) _).symm
    have hgraph :
        (((S - 1) * ((S - j) + (S + A)) -
          Nat.choose ((S - j) + 1) 2 : Nat) : ℝ) =
          3 / 2 * (S : ℝ) ^ 2 + (A : ℝ) * (S : ℝ) -
            5 / 2 * (S : ℝ) - (A : ℝ) +
            3 / 2 * (j : ℝ) - 1 / 2 * (j : ℝ) ^ 2 := hE
    have hquad (L : ℝ) :
        (j : ℝ) * L + 3 / 2 * (j : ℝ) - 1 / 2 * (j : ℝ) ^ 2 ≤
          1 / 2 * (L + 3 / 2) ^ 2 := by
      nlinarith [sq_nonneg ((j : ℝ) - L - 3 / 2)]
    have hchoose_exp :
        (Nat.choose (S + A) (S - j) : ℝ) ≤
          Real.rpow 2 ((A : ℝ) * Real.log (8 * (S + A) / A) /
            Real.log 2 + (j : ℝ) * Real.log (S + A) / Real.log 2) := by
      by_cases hAz : A = 0
      · subst A
        have hcp : (Nat.choose S j : ℝ) ≤ (S : ℝ) ^ j := by
          exact_mod_cast Nat.choose_le_pow S j
        have hp := hpow_log (x := (S : ℝ)) (by positivity) j
        simp only [Nat.cast_zero, zero_mul, zero_div, zero_add]
        rw [hchooseeq]
        convert hcp.trans_eq hp using 1 <;> ring
      · have hAp : 1 ≤ A := Nat.one_le_iff_ne_zero.mpr hAz
        have hc := hchoose_split (S + A) A j hAp
        rw [hchooseeq]
        have hxpos : 0 < 8 * (S + A : ℝ) / A := by positivity
        have hkpos : 0 < (S + A : ℝ) := by positivity
        have hp1 := hpow_log hxpos A
        have hp2 := hpow_log hkpos j
        calc
          (Nat.choose (S + A) (A + j) : ℝ) ≤
              (8 * (S + A : ℝ) / A) ^ A * (S + A : ℝ) ^ j := by
                simpa using hc
          _ = Real.rpow 2 ((A : ℝ) *
                (Real.log (8 * (S + A) / A) / Real.log 2)) *
                Real.rpow 2 ((j : ℝ) *
                  (Real.log (S + A) / Real.log 2)) := by rw [hp1, hp2]
          _ = Real.rpow 2 ((A : ℝ) * Real.log (8 * (S + A) / A) /
                Real.log 2 + (j : ℝ) * Real.log (S + A) / Real.log 2) := by
                calc
                  _ = Real.rpow 2
                      ((A : ℝ) * (Real.log (8 * (S + A) / A) / Real.log 2) +
                        (j : ℝ) * (Real.log (S + A) / Real.log 2)) :=
                    (Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _).symm
                  _ = _ := by congr 1 <;> ring
    have hAlog : (A : ℝ) * Real.log (8 * (S + A) / A) / Real.log 2 ≤
        1000 * Real.sqrt ((A : ℝ) * (S : ℝ)) := by
      by_cases hAz : A = 0
      · subst A
        simp
      · have hAp : 0 < (A : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hAz)
        have hX1 : (1 : ℝ) ≤ 8 * (S + A) / A := by
          apply (le_div_iff₀ hAp).2
          have hAreal : (A : ℝ) ≤ (S : ℝ) := by exact_mod_cast hA
          have : (A : ℝ) ≤ 8 * (S + A) := by nlinarith
          nlinarith
        have hXupper : 8 * (S + A : ℝ) / A ≤ 16 * S / A := by
          apply (div_le_div_of_nonneg_right ?_ (le_of_lt hAp))
          have hASreal : (A : ℝ) ≤ (S : ℝ) := by exact_mod_cast hA
          nlinarith
        have hlogX := hlog2_le_sqrt hX1
        have hroot := hsqrt_ratio (A := (A : ℝ)) (S := (S : ℝ))
          (X := 8 * (S + A : ℝ) / A) hAp
          (by exact_mod_cast hA) hXupper (by positivity)
        have hmul := mul_le_mul_of_nonneg_left hlogX (le_of_lt hAp)
        calc
          (A : ℝ) * Real.log (8 * (S + A) / A) / Real.log 2 =
              (A : ℝ) * (Real.log (8 * (S + A) / A) / Real.log 2) := by ring
          _ ≤ (A : ℝ) * (4 * Real.sqrt (8 * (S + A) / A)) := hmul
          _ = 4 * ((A : ℝ) * Real.sqrt (8 * (S + A) / A)) := by ring
          _ ≤ 16 * Real.sqrt ((A : ℝ) * (S : ℝ)) := by
            have hroot4 := mul_le_mul_of_nonneg_left hroot
              (by norm_num : (0 : ℝ) ≤ 4)
            nlinarith
          _ ≤ 1000 * Real.sqrt ((A : ℝ) * (S : ℝ)) := by
            gcongr
            norm_num
    have hLbound : Real.log (S + A) / Real.log 2 ≤
        16 * Real.sqrt (S : ℝ) := by
      have hK1 : (1 : ℝ) ≤ S + A := by
        have hSreal : (2 : ℝ) ≤ S := by exact_mod_cast hS
        nlinarith
      have hlogK := hlog2_le_fourth hK1
      have hKS : (S + A : ℝ) ≤ 2 * S := by
        have hASreal : (A : ℝ) ≤ (S : ℝ) := by exact_mod_cast hA
        nlinarith
      have hsqrtK : Real.sqrt (S + A : ℝ) ≤ 2 * Real.sqrt S := by
        rw [Real.sqrt_le_left (by positivity : 0 ≤ 2 * Real.sqrt S)]
        have hsqS : (Real.sqrt (S : ℝ)) ^ 2 = S := Real.sq_sqrt hS0
        have hSreal : (2 : ℝ) ≤ S := by exact_mod_cast hS
        nlinarith [hKS, hsqS, hSreal, sq_nonneg (Real.sqrt S)]
      have hsqrtS0 : 0 ≤ Real.sqrt (S : ℝ) := Real.sqrt_nonneg _
      have hq : Real.sqrt (Real.sqrt (S + A : ℝ)) ≤
          2 * Real.sqrt (S : ℝ) := by
        have hq0 : 0 ≤ Real.sqrt (Real.sqrt (S + A : ℝ)) := Real.sqrt_nonneg _
        have hq2 : (Real.sqrt (Real.sqrt (S + A : ℝ))) ^ 2 =
            Real.sqrt (S + A : ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
        have hsqrtS_le : Real.sqrt (S : ℝ) ≤ S := by
          rw [Real.sqrt_le_left hS0]
          have hSreal : (2 : ℝ) ≤ S := by exact_mod_cast hS
          nlinarith [Real.sq_sqrt hS0, hSreal]
        have hsq : (Real.sqrt (Real.sqrt (S + A : ℝ))) ^ 2 ≤
            (2 * Real.sqrt (S : ℝ)) ^ 2 := by
          rw [hq2, mul_pow, Real.sq_sqrt hS0]
          nlinarith [hsqrtK, hsqrtS_le]
        exact (sq_le_sq₀ hq0 (by positivity)).mp hsq
      have hq8 := mul_le_mul_of_nonneg_left hq (by norm_num : (0 : ℝ) ≤ 8)
      calc
        Real.log (S + A) / Real.log 2 ≤
            8 * Real.sqrt (Real.sqrt (S + A : ℝ)) := hlogK
        _ ≤ 16 * Real.sqrt (S : ℝ) := by nlinarith [hq8]
    have hplus :
        1 / 2 * (Real.log (S + A) / Real.log 2 + 3 / 2) ^ 2 ≤
          10000 * Real.sqrt (S : ℝ) := by
      let L : ℝ := Real.log (S + A) / Real.log 2
      have hL0 : 0 ≤ L := by
        dsimp [L]
        have hK1 : (1 : ℝ) ≤ S + A := by
          have hSreal : (2 : ℝ) ≤ S := by exact_mod_cast hS
          nlinarith
        have hlog0 : 0 ≤ Real.log (S + A) := Real.log_nonneg hK1
        have hlogtwo0 : 0 < Real.log 2 := by linarith [hlogtwo]
        positivity
      have hL := hLbound
      have hLsq : L ^ 2 ≤ 128 * Real.sqrt (S : ℝ) := by
        have hK1 : (1 : ℝ) ≤ S + A := by
          have hSreal : (2 : ℝ) ≤ S := by exact_mod_cast hS
          nlinarith
        have hlogK := hlog2_le_fourth hK1
        have hKS : (S + A : ℝ) ≤ 2 * S := by
          have hASreal : (A : ℝ) ≤ (S : ℝ) := by exact_mod_cast hA
          nlinarith
        have hsqrtK : Real.sqrt (S + A : ℝ) ≤ 2 * Real.sqrt S := by
          rw [Real.sqrt_le_left (by positivity : 0 ≤ 2 * Real.sqrt S)]
          have hsqS : (Real.sqrt (S : ℝ)) ^ 2 = S := Real.sq_sqrt hS0
          have hSreal : (2 : ℝ) ≤ S := by exact_mod_cast hS
          nlinarith [hKS, hsqS, hSreal, sq_nonneg (Real.sqrt S)]
        have hq2 : (Real.sqrt (Real.sqrt (S + A : ℝ))) ^ 2 =
            Real.sqrt (S + A : ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
        have hq0 : 0 ≤ Real.sqrt (Real.sqrt (S + A : ℝ)) := Real.sqrt_nonneg _
        have hLq : L ≤ 8 * Real.sqrt (Real.sqrt (S + A : ℝ)) := by
          dsimp [L]
          exact hlogK
        have hsq := mul_self_le_mul_self hL0 hLq
        dsimp [L] at hsq ⊢
        nlinarith [hq2, hsqrtK, sq_nonneg (Real.sqrt S)]
      have hLupper : L ≤ 16 * Real.sqrt (S : ℝ) := by
        dsimp [L]
        exact hLbound
      have hsqplus : (L + 3 / 2) ^ 2 ≤
          (16 * Real.sqrt (S : ℝ) + 3 / 2) ^ 2 := by
        have hsqplus' := mul_self_le_mul_self
          (by positivity : 0 ≤ L + 3 / 2)
          (show L + 3 / 2 ≤ 16 * Real.sqrt (S : ℝ) + 3 / 2 by
            nlinarith [hLupper])
        simpa [pow_two] using hsqplus'
      have hsqrtS1 : 1 ≤ Real.sqrt (S : ℝ) := by
        apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) hS0).2
        have hSreal : (2 : ℝ) ≤ S := by exact_mod_cast hS
        norm_num
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega : S ≠ 0))
      nlinarith [hLsq, hsqplus]
    have hexp :
        (A : ℝ) * Real.log (8 * (S + A) / A) / Real.log 2 +
            (j : ℝ) * Real.log (S + A) / Real.log 2 +
            (((S - 1) * ((S - j) + (S + A)) -
              Nat.choose ((S - j) + 1) 2 : Nat) : ℝ) ≤
          3 / 2 * (S : ℝ) ^ 2 + (A : ℝ) * (S : ℝ) -
            5 / 2 * (S : ℝ) +
            1000 * Real.sqrt ((A : ℝ) * (S : ℝ)) +
            10000 * Real.sqrt (S : ℝ) := by
      rw [hgraph]
      have hquad' := hquad (Real.log (S + A) / Real.log 2)
      calc
        _ ≤ 3 / 2 * (S : ℝ) ^ 2 + (A : ℝ) * (S : ℝ) -
            5 / 2 * (S : ℝ) - (A : ℝ) +
            (A : ℝ) * Real.log (8 * (S + A) / A) / Real.log 2 +
            1 / 2 * (Real.log (S + A) / Real.log 2 + 3 / 2) ^ 2 := by
              have hquad'' :
                  (j : ℝ) * Real.log (S + A) / Real.log 2 +
                    3 / 2 * (j : ℝ) - 1 / 2 * (j : ℝ) ^ 2 ≤
                  1 / 2 * (Real.log (S + A) / Real.log 2 + 3 / 2) ^ 2 := by
                convert hquad' using 1 <;> ring
              linarith [hquad'']
        _ ≤ _ := by nlinarith [hAlog, hplus, hA0]
    calc
      ((Nat.choose (S + A) (S - j) *
        2 ^ ((S - 1) * ((S - j) + (S + A)) -
          Nat.choose ((S - j) + 1) 2) : Nat) : ℝ) =
          (Nat.choose (S + A) (S - j) : ℝ) *
            Real.rpow 2 (((S - 1) * ((S - j) + (S + A)) -
              Nat.choose ((S - j) + 1) 2 : Nat) : ℝ) := hcast
      _ ≤ Real.rpow 2
            ((A : ℝ) * Real.log (8 * (S + A) / A) / Real.log 2 +
              (j : ℝ) * Real.log (S + A) / Real.log 2) *
            Real.rpow 2 (((S - 1) * ((S - j) + (S + A)) -
              Nat.choose ((S - j) + 1) 2 : Nat) : ℝ) := by
        apply mul_le_mul_of_nonneg_right _
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
        exact hchoose_exp
      _ = Real.rpow 2
          ((A : ℝ) * Real.log (8 * (S + A) / A) / Real.log 2 +
            (j : ℝ) * Real.log (S + A) / Real.log 2 +
            (((S - 1) * ((S - j) + (S + A)) -
              Nat.choose ((S - j) + 1) 2 : Nat) : ℝ)) := by
        exact (Real.rpow_add (by norm_num : (0 : ℝ) < 2)
          ((A : ℝ) * Real.log (8 * (S + A) / A) / Real.log 2 +
            (j : ℝ) * Real.log (S + A) / Real.log 2)
          (((S - 1) * ((S - j) + (S + A)) -
            Nat.choose ((S - j) + 1) 2 : Nat) : ℝ)).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  
  have hsum (S A : Nat) (hS : 2 ≤ S) (hA : A ≤ S) :
    (∑ t ∈ Finset.Icc 1 (S - 1),
      (Nat.choose (S + A) t *
        2 ^ ((S - 1) * (t + (S + A)) - Nat.choose (t + 1) 2) : Nat) : ℝ) ≤
      Real.rpow 2
        (3 / 2 * (S : ℝ) ^ 2 + (A : ℝ) * (S : ℝ) -
          5 / 2 * (S : ℝ) +
          1000 * Real.sqrt ((A : ℝ) * (S : ℝ)) +
          20000 * Real.sqrt (S : ℝ)) := by
    have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h ⊢
      linarith
    have hlog2_le_sqrt {x : ℝ} (hx : 1 ≤ x) :
        Real.log x / Real.log 2 ≤ 4 * Real.sqrt x := by
      have hx0 : 0 ≤ x := (by norm_num : (0 : ℝ) ≤ 1).trans hx
      have hlog : Real.log x ≤ 2 * Real.sqrt x := by
        have hsx : 1 ≤ Real.sqrt x := by
          apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) hx0).2
          nlinarith
        calc
          Real.log x = 2 * Real.log (Real.sqrt x) := by
            rw [Real.log_sqrt hx0]
            ring
          _ ≤ 2 * (Real.sqrt x - 1) := by
            gcongr
            exact Real.log_le_sub_one_of_pos (by positivity)
          _ ≤ 2 * Real.sqrt x := by nlinarith
      have hlogtwo0 : 0 < Real.log 2 := by linarith
      apply (div_le_iff₀ hlogtwo0).2
      have hmul := mul_le_mul_of_nonneg_right hlogtwo (Real.sqrt_nonneg x)
      nlinarith
  
    let R : ℝ := Real.rpow 2
          (3 / 2 * (S : ℝ) ^ 2 + (A : ℝ) * (S : ℝ) -
            5 / 2 * (S : ℝ) +
            1000 * Real.sqrt ((A : ℝ) * (S : ℝ)) +
            10000 * Real.sqrt (S : ℝ))
    have hterm : ∀ t ∈ Finset.Icc 1 (S - 1),
        ((Nat.choose (S + A) t *
          2 ^ ((S - 1) * (t + (S + A)) - Nat.choose (t + 1) 2) : Nat) : ℝ) ≤ R := by
      intro t ht
      have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
      have htS : t ≤ S - 1 := (Finset.mem_Icc.mp ht).2
      let j := S - t
      have hj : 1 ≤ j := by dsimp [j]; omega
      have hjS : j ≤ S - 1 := by dsimp [j]; omega
      have hp := hpoint S A j hS hA hj hjS
      have hsj : S - j = t := by dsimp [j]; omega
      simpa [R, hsj] using hp
    have hsumR :
        (∑ t ∈ Finset.Icc 1 (S - 1),
          (Nat.choose (S + A) t *
            2 ^ ((S - 1) * (t + (S + A)) - Nat.choose (t + 1) 2) : Nat) : ℝ) ≤
          (S : ℝ) * R := by
      calc
        (∑ x ∈ Finset.Icc 1 (S - 1),
            (((Nat.choose (S + A) x *
              2 ^ ((S - 1) * (x + (S + A)) - Nat.choose (x + 1) 2) : Nat) : ℝ))) ≤
            ∑ _x ∈ Finset.Icc 1 (S - 1), R := by
              apply Finset.sum_le_sum
              intro x hx
              exact hterm x hx
        _ = ((Finset.Icc 1 (S - 1)).card : ℝ) * R := by simp
        _ ≤ (S : ℝ) * R := by
          have hsub : Finset.Icc 1 (S - 1) ⊆ Finset.range S := by
            intro x hx
            simp only [Finset.mem_Icc, Finset.mem_range] at hx ⊢
            omega
          have hcard := Finset.card_le_card hsub
          have hR0 : 0 ≤ R := by dsimp [R]; positivity
          have hcardreal : (Finset.Icc 1 (S - 1)).card ≤ (S : ℝ) := by
            calc
              ((Finset.Icc 1 (S - 1)).card : ℝ) ≤
                  (Finset.range S).card := by exact_mod_cast hcard
              _ = S := by simp
          exact mul_le_mul_of_nonneg_right hcardreal hR0
    have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg _
    have hS1 : (1 : ℝ) ≤ S := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega : S ≠ 0))
    have hR : (S : ℝ) * R ≤ Real.rpow 2
        (3 / 2 * (S : ℝ) ^ 2 + (A : ℝ) * (S : ℝ) -
          5 / 2 * (S : ℝ) +
          1000 * Real.sqrt ((A : ℝ) * (S : ℝ)) +
          20000 * Real.sqrt (S : ℝ)) := by
      have hSpos : 0 < (S : ℝ) := by positivity
      have hlogrep : Real.rpow 2 (Real.log (S : ℝ) / Real.log 2) = S := by
        calc
          Real.rpow 2 (Real.log (S : ℝ) / Real.log 2) =
              Real.exp (Real.log 2 * (Real.log (S : ℝ) / Real.log 2)) :=
                Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) _
          _ = Real.exp (Real.log (S : ℝ)) := by
            congr 1
            field_simp
          _ = S := Real.exp_log hSpos
      have hlogS := hlog2_le_sqrt (x := (S : ℝ)) hS1
      have hSfactor : (S : ℝ) ≤ Real.rpow 2 (4 * Real.sqrt (S : ℝ)) := by
        calc
          (S : ℝ) = Real.rpow 2 (Real.log (S : ℝ) / Real.log 2) := hlogrep.symm
          _ ≤ Real.rpow 2 (4 * Real.sqrt (S : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hlogS
      have hnonR : 0 ≤ R := by dsimp [R]; positivity
      calc
        (S : ℝ) * R ≤ Real.rpow 2 (4 * Real.sqrt (S : ℝ)) * R :=
          mul_le_mul_of_nonneg_right hSfactor hnonR
        _ = Real.rpow 2
            (4 * Real.sqrt (S : ℝ) +
              (3 / 2 * (S : ℝ) ^ 2 + (A : ℝ) * (S : ℝ) -
                5 / 2 * (S : ℝ) +
                1000 * Real.sqrt ((A : ℝ) * (S : ℝ)) +
                10000 * Real.sqrt (S : ℝ))) := by
          dsimp [R]
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
          nlinarith [Real.sqrt_nonneg (S : ℝ)])
    exact hsumR.trans hR
  let e : Nat → ℝ := fun n =>
    1000 * Real.sqrt ((a n : ℝ) * (s n : ℝ)) + 20000 * Real.sqrt (s n : ℝ)
  have he : (fun n => e n) =o[Filter.atTop] (fun n => (s n : ℝ)) := by
    have h1 := hprod_littleo.const_mul_left (1000 : ℝ)
    have h2 := (hsqrt_littleo s hs).const_mul_left (20000 : ℝ)
    have h3 := h1.add h2
    simpa [e] using h3
  refine ⟨e, he, ?_⟩
  have hS2 : ∀ᶠ n in Filter.atTop, 2 ≤ s n := hs.eventually_ge_atTop 2
  have hA1 : ∀ᶠ n in Filter.atTop, a n ≤ s n := by
    have hone : (0 : ℝ) < 1 := by norm_num
    filter_upwards [ha.def hone] with n hn
    have ha0 : (0 : ℝ) ≤ (a n : ℝ) := Nat.cast_nonneg _
    have hs0 : (0 : ℝ) ≤ (s n : ℝ) := Nat.cast_nonneg _
    have hn' : (a n : ℝ) ≤ (s n : ℝ) := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg ha0, abs_of_nonneg hs0, one_mul] using hn
    exact_mod_cast hn'
  filter_upwards [hS2, hA1] with n hnS hnA
  dsimp [e]
  convert hsum (s n) (a n) hnS hnA using 1
  congr 1
  ring
