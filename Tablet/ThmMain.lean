import Tablet.DStarCounting
import Tablet.FiniteRamseyPositivity
import Tablet.RandomPermutationReduction
import Tablet.SamplingDeletion

set_option maxHeartbeats 1000000

-- [TABLET NODE: ThmMain]
theorem ThmMain :
    ∀ s : Nat, 3 ≤ s → ∃ c : ℝ, 0 < c ∧
      ∀ k : Nat, 2 ≤ k →
        (RamseyNumber s k : ℝ) ≥
          c * (k : ℝ) ^ (s - 1) /
            (Real.log (k : ℝ)) ^ (2 * s - 4) := by
-- BODY
  classical
  intro s hs
  let t : Nat := s - 1
  have ht : 2 ≤ t := by dsimp [t]; omega
  obtain ⟨C, hC, hD⟩ := DStarCounting t ht
  have hCR : 0 < (C : ℝ) := by exact_mod_cast hC
  have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  let B : ℝ :=
    (1 / (8 * Real.exp 1 * (C : ℝ))) *
      (1 / (16 * (C : ℝ))) ^ (t - 1)
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hlittle2 :
      (fun x : ℝ => Real.log x ^ 2) =o[Filter.atTop] id :=
    Real.isLittleO_pow_log_id_atTop
  have hlittle4 :
      (fun x : ℝ => Real.log x ^ 4) =o[Filter.atTop] id :=
    Real.isLittleO_pow_log_id_atTop
  have hlittleb :
      (fun x : ℝ => Real.log x ^ (2 * t - 2)) =o[Filter.atTop] id :=
    Real.isLittleO_pow_log_id_atTop
  have he2 : ∀ᶠ k : Nat in Filter.atTop,
      (Real.log (k : ℝ)) ^ 2 ≤
        (1 / (16 * (C : ℝ) ^ 2)) * (k : ℝ) := by
    have h := (hlittle2.natCast_atTop).bound (by positivity :
      (0 : ℝ) < 1 / (16 * (C : ℝ) ^ 2))
    filter_upwards [h] with k hk
    have hklog : 0 ≤ Real.log (k : ℝ) ^ 2 := sq_nonneg _
    have hk0 : 0 ≤ (k : ℝ) := by positivity
    simpa [Real.norm_eq_abs, abs_of_nonneg hklog, abs_of_nonneg hk0] using hk
  have he4 : ∀ᶠ k : Nat in Filter.atTop,
      (Real.log (k : ℝ)) ^ 4 ≤
        (1 / (64 * (C : ℝ))) * (k : ℝ) := by
    have h := (hlittle4.natCast_atTop).bound (by positivity :
      (0 : ℝ) < 1 / (64 * (C : ℝ)))
    filter_upwards [h] with k hk
    have hklog : 0 ≤ Real.log (k : ℝ) ^ 4 := by positivity
    have hk0 : 0 ≤ (k : ℝ) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hklog] at hk
    simpa [id, abs_of_nonneg hk0] using hk
  have heb : ∀ᶠ k : Nat in Filter.atTop,
      (Real.log (k : ℝ)) ^ (2 * t - 2) ≤ (B / 2) * (k : ℝ) := by
    have h := (hlittleb.natCast_atTop).bound (by linarith : (0 : ℝ) < B / 2)
    filter_upwards [h] with k hk
    have hklog : 0 ≤ Real.log (k : ℝ) ^ (2 * t - 2) := by positivity
    have hk0 : 0 ≤ (k : ℝ) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hklog] at hk
    simpa [id, abs_of_nonneg hk0] using hk
  have hEv : ∀ᶠ k : Nat in Filter.atTop,
      2 ≤ k ∧
      (Real.log (k : ℝ)) ^ 2 ≤
        (1 / (16 * (C : ℝ) ^ 2)) * (k : ℝ) ∧
      (Real.log (k : ℝ)) ^ 4 ≤
        (1 / (64 * (C : ℝ))) * (k : ℝ) ∧
      (Real.log (k : ℝ)) ^ (2 * t - 2) ≤ (B / 2) * (k : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop (2 : Nat), he2, he4, heb]
    tauto
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hEv
  have hLlog : ∀ {k : Nat}, 2 ≤ k →
      (Nat.log 2 k : ℝ) ≤ 2 * Real.log (k : ℝ) := by
    intro k hk
    have hk0 : (k : ℝ) > 0 := by positivity
    have hp : (2 ^ Nat.log 2 k : Nat) ≤ k := Nat.pow_log_le_self 2 (by omega)
    have hpR : ((2 ^ Nat.log 2 k : Nat) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hp
    have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 ^ Nat.log 2 k : Nat)) hpR
    rw [Nat.cast_pow, Real.log_pow] at hlog
    have hLnonneg : (0 : ℝ) ≤ Nat.log 2 k := by positivity
    have hprod := mul_le_mul_of_nonneg_left hlogtwo hLnonneg
    have hhalf : (Nat.log 2 k : ℝ) / 2 ≤ Real.log (k : ℝ) := by
      calc
        (Nat.log 2 k : ℝ) / 2 = (Nat.log 2 k : ℝ) * (1 / 2) := by ring
        _ ≤ (Nat.log 2 k : ℝ) * Real.log 2 := hprod
        _ ≤ Real.log (k : ℝ) := hlog
    nlinarith
  let M : ℝ := (2 : ℝ) ^ (2 * t - 2) * (N + 1 : ℝ) ^ t
  have hM : 0 < M := by
    dsimp [M]
    positivity
  let c : ℝ := min (B / 2) (1 / M)
  have hc : 0 < c := by
    dsimp [c]
    exact lt_min (by linarith) (by positivity)
  refine ⟨c, hc, ?_⟩
  intro k hk
  by_cases hlarge : N ≤ k
  · have hev := hN k hlarge
    have hLpos : 0 < Nat.log 2 k := Nat.log_pos (by norm_num) hk
    have hLpow2 : (Nat.log 2 k : ℝ) ^ 2 ≤
        4 * (Real.log (k : ℝ)) ^ 2 := by
      have hlogpos : 0 < Real.log (k : ℝ) := Real.log_pos (by
        exact_mod_cast hk)
      have hLnonneg : (0 : ℝ) ≤ Nat.log 2 k := by positivity
      have hh := hLlog hk
      nlinarith [sq_nonneg ((Nat.log 2 k : ℝ) - 2 * Real.log (k : ℝ))]
    have hLpow4 : (Nat.log 2 k : ℝ) ^ 4 ≤
        16 * (Real.log (k : ℝ)) ^ 4 := by
      have hLnonneg : (0 : ℝ) ≤ Nat.log 2 k := by positivity
      have hlognonneg : 0 ≤ Real.log (k : ℝ) := by
        exact (Real.log_pos (by exact_mod_cast hk)).le
      have hsq := hLpow2
      nlinarith [sq_nonneg ((Nat.log 2 k : ℝ) ^ 2 -
        4 * (Real.log (k : ℝ)) ^ 2)]
    have h4R :
        4 * (C : ℝ) ^ 2 * (Nat.log 2 k : ℝ) ^ 2 ≤ (k : ℝ) := by
      have hh := mul_le_mul_of_nonneg_left hLpow2
        (by positivity : (0 : ℝ) ≤ 4 * (C : ℝ) ^ 2)
      have hhe := mul_le_mul_of_nonneg_left hev.2.1
        (by positivity : (0 : ℝ) ≤ 16 * (C : ℝ) ^ 2)
      calc
        4 * (C : ℝ) ^ 2 * (Nat.log 2 k : ℝ) ^ 2 ≤
            4 * (C : ℝ) ^ 2 * (4 * Real.log (k : ℝ) ^ 2) := hh
        _ = 16 * (C : ℝ) ^ 2 * Real.log (k : ℝ) ^ 2 := by ring
        _ ≤ 16 * (C : ℝ) ^ 2 *
            (1 / (16 * (C : ℝ) ^ 2) * (k : ℝ)) := hhe
        _ = (k : ℝ) := by field_simp
    have h4R' :
        4 * (C : ℝ) * (Nat.log 2 k : ℝ) ^ 4 ≤ (k : ℝ) := by
      have hh := mul_le_mul_of_nonneg_left hLpow4
        (by positivity : (0 : ℝ) ≤ 4 * (C : ℝ))
      have hhe := mul_le_mul_of_nonneg_left hev.2.2.1
        (by positivity : (0 : ℝ) ≤ 64 * (C : ℝ))
      calc
        4 * (C : ℝ) * (Nat.log 2 k : ℝ) ^ 4 ≤
            4 * (C : ℝ) * (16 * Real.log (k : ℝ) ^ 4) := hh
        _ = 64 * (C : ℝ) * Real.log (k : ℝ) ^ 4 := by ring
        _ ≤ 64 * (C : ℝ) *
            (1 / (64 * (C : ℝ)) * (k : ℝ)) := hhe
        _ = (k : ℝ) := by field_simp
    let L : Nat := Nat.log 2 k
    let d : Nat := C * L ^ 2
    let n : Nat := k / d
    let m : Nat := Nat.log 2 n
    let q : Nat := 2 ^ m
    have hLpos' : 0 < L := by simpa [L] using hLpos
    have hdpos : 0 < d := by
      dsimp [d]
      positivity
    have h4Nat : 4 * C ^ 2 * L ^ 2 ≤ k := by
      exact_mod_cast h4R
    have hnd : n * d ≤ k := by
      dsimp [n]
      exact Nat.div_mul_le_self k d
    have hn4C : 4 * C ≤ n := by
      apply (Nat.le_div_iff_mul_le hdpos).2
      convert h4Nat using 1 <;> simp [d] <;> ring
    have hnpos : 0 < n := by omega
    have hnk : n ≤ k := by
      dsimp [n]
      exact Nat.div_le_self k d
    have hqle : q ≤ n := by
      dsimp [q, m]
      exact Nat.pow_log_le_self 2 (by omega)
    have hnlt : n < 2 * q := by
      have hh := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
      dsimp [q, m]
      simpa [Nat.pow_succ, Nat.mul_comm] using hh
    have hqC : C ≤ q := by omega
    have hmL : m ≤ L := by
      dsimp [m, L]
      exact Nat.log_mono_right hnk
    have hthreshold : C * q * m ^ 2 ≤ k := by
      have hmul : C * q * m ^ 2 ≤ C * n * L ^ 2 := by
        gcongr
      have hnd' : C * n * L ^ 2 ≤ k := by
        simpa [d, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hnd
      exact hmul.trans hnd'
    obtain ⟨D, hDfree, hDcard, hDcount⟩ :=
      hD q hqC ⟨m, by rfl⟩ k (by simpa [L, m, q] using hthreshold)
    have hqpos : 0 < q := by omega
    have hupperNat : k < 2 * n * d := by
      have hquot : k < (n + 1) * d := by
        apply (Nat.div_lt_iff_lt_mul hdpos).1
        exact Nat.lt_succ_self n
      have hn1 : n + 1 ≤ 2 * n := by omega
      exact lt_of_lt_of_le hquot (by
        nlinarith)
    have hqreal :
        (k : ℝ) / (4 * (C : ℝ) * (L : ℝ) ^ 2) < (q : ℝ) := by
      have hnltR : (n : ℝ) < 2 * (q : ℝ) := by exact_mod_cast hnlt
      have hupperR : (k : ℝ) < 2 * (n : ℝ) * (d : ℝ) := by
        exact_mod_cast hupperNat
      have hdR : (d : ℝ) = (C : ℝ) * (L : ℝ) ^ 2 := by
        simp [d, L, Nat.cast_mul, Nat.cast_pow]
      have hden : 0 < 4 * (C : ℝ) * (L : ℝ) ^ 2 := by positivity
      apply (div_lt_iff₀ hden).2
      have hqmul : (k : ℝ) < 2 * (q : ℝ) *
          (2 * ((C : ℝ) * (L : ℝ) ^ 2)) := by
        calc
          (k : ℝ) < 2 * (n : ℝ) * ((C : ℝ) * (L : ℝ) ^ 2) := by
            calc
              (k : ℝ) < 2 * (n : ℝ) * (d : ℝ) := hupperR
              _ = 2 * (n : ℝ) * ((C : ℝ) * (L : ℝ) ^ 2) := by rw [hdR]
          _ < 2 * (2 * (q : ℝ)) * ((C : ℝ) * (L : ℝ) ^ 2) := by
            gcongr
          _ = 2 * (q : ℝ) * (2 * ((C : ℝ) * (L : ℝ) ^ 2)) := by ring
      calc
        (k : ℝ) < 2 * (q : ℝ) *
            (2 * ((C : ℝ) * (L : ℝ) ^ 2)) := hqmul
        _ = (q : ℝ) * (4 * (C : ℝ) * (L : ℝ) ^ 2) := by ring
    have hqL : (L : ℝ) ^ 2 ≤ (q : ℝ) := by
      have h4real : 4 * (C : ℝ) * (L : ℝ) ^ 4 ≤ (k : ℝ) := by
        simpa [L] using h4R'
      have hden : 0 < 4 * (C : ℝ) * (L : ℝ) ^ 2 := by positivity
      have hratio : (L : ℝ) ^ 2 ≤
          (k : ℝ) / (4 * (C : ℝ) * (L : ℝ) ^ 2) := by
        apply (le_div_iff₀ hden).2
        nlinarith [h4real]
      exact hratio.trans_lt hqreal |>.le
    have hqLNat : L ^ 2 ≤ q := by exact_mod_cast hqL
    have hquot : k < (n + 1) * d := by
      apply (Nat.div_lt_iff_lt_mul hdpos).1
      exact Nat.lt_succ_self n
    have hn1q : n + 1 ≤ 2 * q := by omega
    have hdCq : d ≤ C * q := by
      dsimp [d]
      gcongr
    have hkupperNat : k < 2 * C * q ^ 2 := by
      calc
        k < (n + 1) * d := hquot
        _ ≤ (2 * q) * (C * q) := Nat.mul_le_mul hn1q hdCq
        _ = 2 * C * q ^ 2 := by ring
    have hqpowNat : q ^ 2 ≤ q ^ t := by
      apply Nat.pow_le_pow_right
      · omega
      · exact ht
    have hkupper : (k : ℝ) <
        Real.exp 1 * (C : ℝ) * (q : ℝ) ^ t := by
      have hkn : (k : ℝ) < 2 * (C : ℝ) * (q : ℝ) ^ 2 := by
        exact_mod_cast hkupperNat
      have hqp : (q : ℝ) ^ 2 ≤ (q : ℝ) ^ t := by exact_mod_cast hqpowNat
      have hexp : (2 : ℝ) < Real.exp 1 := by
        have hh := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
        norm_num at hh ⊢
        exact hh
      have hkn' : (k : ℝ) < 2 * (C : ℝ) * (q : ℝ) ^ t :=
        lt_of_lt_of_le hkn (mul_le_mul_of_nonneg_left hqp (by positivity))
      exact hkn'.trans (by
        have hh := mul_lt_mul_of_pos_right hexp
          (by positivity : 0 < (C : ℝ) * (q : ℝ) ^ t)
        simpa [mul_assoc] using hh)
    let p : ℝ :=
      (k : ℝ) / (Real.exp 1 * (C : ℝ) * (q : ℝ) ^ t)
    have hp0 : 0 ≤ p := by
      dsimp [p]
      positivity
    have hp1 : p ≤ 1 := by
      apply (div_le_iff₀ (by positivity :
        0 < Real.exp 1 * (C : ℝ) * (q : ℝ) ^ t)).2
      simpa using hkupper.le
    obtain ⟨G, hGcard, hGloop, hGfree, hGcount⟩ :=
      RandomPermutationReduction D s k (by
        have hts : t + 1 = s := by dsimp [t]; omega
        intro hs'
        apply hDfree
        simpa [hts] using hs') (by omega)
    have hI : (IndependentSetCount G k : ℝ) ≤
        (Real.exp 1 / (k : ℝ)) ^ k *
          ((C : ℝ) * (q : ℝ) ^ t) ^ k := by
      calc
        (IndependentSetCount G k : ℝ) ≤
            (Real.exp 1 / (k : ℝ)) ^ k *
              (ForwardIndependentCount D k : ℝ) := hGcount
        _ ≤ (Real.exp 1 / (k : ℝ)) ^ k *
            ((C : ℝ) * (q : ℝ) ^ t) ^ k := by
          gcongr
    have hcancel :
        p * (Real.exp 1 / (k : ℝ)) *
            ((C : ℝ) * (q : ℝ) ^ t) = 1 := by
      dsimp [p]
      field_simp
    have hcount : p ^ k * (IndependentSetCount G k : ℝ) ≤ 1 := by
      calc
        p ^ k * (IndependentSetCount G k : ℝ) ≤
            p ^ k * ((Real.exp 1 / (k : ℝ)) ^ k *
              ((C : ℝ) * (q : ℝ) ^ t) ^ k) := by
                gcongr
        _ = (p * (Real.exp 1 / (k : ℝ)) *
            ((C : ℝ) * (q : ℝ) ^ t)) ^ k := by
              rw [mul_pow, mul_pow]
              ring
        _ = 1 := by rw [hcancel, one_pow]
    have hR := SamplingDeletion G s k hGloop hGfree (by omega)
      p hp0 hp1 hcount
    have hqlog :
        (k : ℝ) / (16 * (C : ℝ) * (Real.log (k : ℝ)) ^ 2) <
          (q : ℝ) := by
      have hlogpos : 0 < Real.log (k : ℝ) :=
        Real.log_pos (by exact_mod_cast hk)
      have hdenL : 0 < 4 * (C : ℝ) * (L : ℝ) ^ 2 := by positivity
      have hdenlog : 0 < 16 * (C : ℝ) * Real.log (k : ℝ) ^ 2 := by
        positivity
      have hdencomp : 4 * (C : ℝ) * (L : ℝ) ^ 2 ≤
          16 * (C : ℝ) * Real.log (k : ℝ) ^ 2 := by
        calc
          4 * (C : ℝ) * (L : ℝ) ^ 2 ≤
              4 * (C : ℝ) * (4 * Real.log (k : ℝ) ^ 2) := by
                gcongr
          _ = 16 * (C : ℝ) * Real.log (k : ℝ) ^ 2 := by ring
      have hfrac := div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ (k : ℝ))
        hdenL hdencomp
      exact lt_of_le_of_lt hfrac hqreal
    have hbasepos : 0 ≤
        (k : ℝ) / (16 * (C : ℝ) * (Real.log (k : ℝ)) ^ 2) := by positivity
    have hqpow :
        ((k : ℝ) / (16 * (C : ℝ) * (Real.log (k : ℝ)) ^ 2)) ^ (t - 1) <
          (q : ℝ) ^ (t - 1) := by
      apply pow_lt_pow_left₀ hqlog hbasepos
      omega
    have hqpow' :
        ((k : ℝ) ^ (t - 1)) /
            ((16 * (C : ℝ) * (Real.log (k : ℝ)) ^ 2) ^ (t - 1)) <
          (q : ℝ) ^ (t - 1) := by
      simpa [div_pow] using hqpow
    have hE : 2 * t - 1 = t + (t - 1) := by omega
    have hqEpos : 0 < (q : ℝ) ^ (2 * t - 1) := by positivity
    have hqEfloor :
        (q ^ (2 * t - 1) / 4 : Nat) >
          ((q : ℝ) ^ (2 * t - 1)) / 8 := by
      let x : Nat := q ^ (2 * t - 1)
      let r : Nat := x / 4
      have hx4 : 4 ≤ x := by
        have hC1 : 1 ≤ C := by omega
        have hfourC : 4 ≤ 4 * C := by omega
        have hn4 : 4 ≤ n := le_trans hfourC hn4C
        have hq3 : 3 ≤ q := by omega
        have hE3 : 3 ≤ 2 * t - 1 := by omega
        calc
          4 ≤ 3 ^ 3 := by norm_num
          _ ≤ q ^ 3 := Nat.pow_le_pow_left hq3 3
          _ ≤ q ^ (2 * t - 1) := Nat.pow_le_pow_right (by omega) hE3
      have hrpos : 0 < r := by
        dsimp [r, x]
        exact (Nat.div_pos_iff).2 ⟨by norm_num, by simpa [x] using hx4⟩
      have hxlt : x < (r + 1) * 4 := by
        apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 4)).1
        exact Nat.lt_succ_self r
      have hxlt' : x < 8 * r := by
        have hr1 : 1 ≤ r := by omega
        calc
          x < (r + 1) * 4 := hxlt
          _ ≤ (2 * r) * 4 := by
            gcongr
            omega
          _ = 8 * r := by ring
      have hxltR : (x : ℝ) < 8 * (r : ℝ) := by exact_mod_cast hxlt'
      have hxr : (x : ℝ) / 8 < (r : ℝ) := by
        apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 8)).2
        simpa [mul_comm] using hxltR
      dsimp [r, x] at hxr ⊢
      rw [Nat.cast_pow] at hxr
      exact hxr
    have hcardR :
        (((q ^ (2 * t - 1) / 4 : Nat) : ℝ)) ≤
          (@Fintype.card G.vertex G.fintype : ℝ) := by
      have hcardNat : q ^ (2 * t - 1) / 4 ≤
          @Fintype.card G.vertex G.fintype := by
        calc
          q ^ (2 * t - 1) / 4 ≤ @Fintype.card D.vertex D.fintype := hDcard
          _ = @Fintype.card G.vertex G.fintype := hGcard.symm
      exact_mod_cast hcardNat
    have hRfloor :
        p * (((q ^ (2 * t - 1) / 4 : Nat) : ℝ)) - 1 <
          (RamseyNumber s k : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hcardR (by positivity : 0 ≤ p)
      exact lt_of_le_of_lt (sub_le_sub_right hmul 1) hR
    have hp_pos : 0 < p := by
      dsimp [p]
      positivity
    have hfloor_lt_card :
        ((q : ℝ) ^ (2 * t - 1)) / 8 <
          (@Fintype.card G.vertex G.fintype : ℝ) := by
      exact hqEfloor.trans_le hcardR
    have hR8 :
        p * (((q : ℝ) ^ (2 * t - 1)) / 8) - 1 <
          (RamseyNumber s k : ℝ) := by
      have hmul := mul_lt_mul_of_pos_left hfloor_lt_card hp_pos
      exact lt_trans (sub_lt_sub_right hmul 1) hR
    have hexact :
        p * (((q : ℝ) ^ (2 * t - 1)) / 8) =
          ((k : ℝ) * (q : ℝ) ^ (t - 1)) /
            (8 * Real.exp 1 * (C : ℝ)) := by
      dsimp [p]
      rw [hE, pow_add]
      field_simp
    have hqterm :
        B * ((k : ℝ) ^ t /
          (Real.log (k : ℝ)) ^ (2 * t - 2)) <
          p * (((q : ℝ) ^ (2 * t - 1)) / 8) := by
      have hfac : 0 < (k : ℝ) /
          (8 * Real.exp 1 * (C : ℝ)) := by positivity
      have hh := mul_lt_mul_of_pos_left hqpow' hfac
      have hb : 2 * t - 2 = 2 * (t - 1) := by omega
      have hdenpow :
          (16 * (C : ℝ) * (Real.log (k : ℝ)) ^ 2) ^ (t - 1) =
            (16 * (C : ℝ)) ^ (t - 1) *
              (Real.log (k : ℝ)) ^ (2 * (t - 1)) := by
        rw [mul_pow, ← pow_mul]
      rw [hdenpow, ← hb] at hh
      have heq :
          B * ((k : ℝ) ^ t /
            (Real.log (k : ℝ)) ^ (2 * t - 2)) =
            (k : ℝ) / (8 * Real.exp 1 * (C : ℝ)) *
              ((k : ℝ) ^ (t - 1) /
                ((16 * (C : ℝ)) ^ (t - 1) *
                  (Real.log (k : ℝ)) ^ (2 * t - 2))) := by
        have hkreal1 : (1 : ℝ) < (k : ℝ) := by
          exact_mod_cast (show 1 < k by omega)
        have hlogpos : 0 < Real.log (k : ℝ) := Real.log_pos hkreal1
        have hCcancel : (C : ℝ) * ((C : ℝ)⁻¹) = 1 :=
          mul_inv_cancel₀ hCR.ne'
        have hCpow :
            (C : ℝ) ^ (t - 1) * ((C : ℝ)⁻¹) ^ (t - 1) = 1 := by
          rw [← mul_pow, hCcancel, one_pow]
        have h16pow :
            (1 / (16 : ℝ)) ^ (t - 1) * (16 : ℝ) ^ (t - 1) = 1 := by
          rw [← mul_pow]
          norm_num
        dsimp [B]
        field_simp [hCR.ne', Real.exp_ne_zero, hlogpos.ne']
        ring_nf
        rw [hCpow, mul_assoc, h16pow]
        have htpow : (k : ℝ) ^ t = (k : ℝ) * (k : ℝ) ^ (t - 1) := by
          calc
            (k : ℝ) ^ t = (k : ℝ) ^ ((t - 1) + 1) := by
              congr 1
              omega
            _ = (k : ℝ) ^ (t - 1) * (k : ℝ) := by
              rw [pow_add, pow_one]
            _ = (k : ℝ) * (k : ℝ) ^ (t - 1) := by ring
        rw [htpow]
        ring
      calc
        B * ((k : ℝ) ^ t /
            (Real.log (k : ℝ)) ^ (2 * t - 2)) =
            (k : ℝ) / (8 * Real.exp 1 * (C : ℝ)) *
              ((k : ℝ) ^ (t - 1) /
                ((16 * (C : ℝ)) ^ (t - 1) *
                  (Real.log (k : ℝ)) ^ (2 * t - 2))) := heq
        _ < (k : ℝ) / (8 * Real.exp 1 * (C : ℝ)) *
            (q : ℝ) ^ (t - 1) := hh
        _ = ((k : ℝ) * (q : ℝ) ^ (t - 1)) /
            (8 * Real.exp 1 * (C : ℝ)) := by ring
        _ = p * (((q : ℝ) ^ (2 * t - 1)) / 8) := hexact.symm
    have hRlarge :
        B * ((k : ℝ) ^ t /
          (Real.log (k : ℝ)) ^ (2 * t - 2)) - 1 <
          (RamseyNumber s k : ℝ) := by
      exact lt_trans (sub_lt_sub_right hqterm 1) hR8
    have hkreal1 : (1 : ℝ) < (k : ℝ) := by
      exact_mod_cast (show 1 < k by omega)
    have hlogpos : 0 < Real.log (k : ℝ) := Real.log_pos hkreal1
    have hlogpowpos : 0 < (Real.log (k : ℝ)) ^ (2 * t - 2) := by
      positivity
    have hkpow1 : (1 : ℝ) ≤ (k : ℝ) ^ (t - 1) := by
      have hkone : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
      exact one_le_pow₀ hkone
    have hBkle : B * (k : ℝ) ≤ B * (k : ℝ) ^ t := by
      calc
        B * (k : ℝ) = B * (k : ℝ) * 1 := by ring
        _ ≤ B * (k : ℝ) * (k : ℝ) ^ (t - 1) := by
          gcongr
        _ = B * (k : ℝ) ^ t := by
          calc
            B * (k : ℝ) * (k : ℝ) ^ (t - 1) =
                B * ((k : ℝ) ^ (t - 1) * (k : ℝ)) := by ring
            _ = B * (k : ℝ) ^ t := by
              congr 2
              calc
                (k : ℝ) ^ (t - 1) * (k : ℝ) =
                    (k : ℝ) ^ ((t - 1) + 1) := by
                      rw [pow_add, pow_one]
                _ = (k : ℝ) ^ t := by congr 1 <;> omega
    have htwoLog :
        2 * (Real.log (k : ℝ)) ^ (2 * t - 2) ≤ B * (k : ℝ) := by
      nlinarith [hev.2.2.2]
    have htwoLogPow :
        2 * (Real.log (k : ℝ)) ^ (2 * t - 2) ≤ B * (k : ℝ) ^ t :=
      htwoLog.trans hBkle
    have hX : 2 ≤ B * ((k : ℝ) ^ t /
        (Real.log (k : ℝ)) ^ (2 * t - 2)) := by
      calc
        2 ≤ (B * (k : ℝ) ^ t) /
            (Real.log (k : ℝ)) ^ (2 * t - 2) :=
          (le_div_iff₀ hlogpowpos).2 (by simpa [mul_comm] using htwoLogPow)
        _ = B * ((k : ℝ) ^ t /
            (Real.log (k : ℝ)) ^ (2 * t - 2)) := by ring
    have hhalf : B / 2 * ((k : ℝ) ^ t /
        (Real.log (k : ℝ)) ^ (2 * t - 2)) ≤
        B * ((k : ℝ) ^ t /
          (Real.log (k : ℝ)) ^ (2 * t - 2)) - 1 := by
      nlinarith [hX]
    have hlargefinal : B / 2 * ((k : ℝ) ^ t /
        (Real.log (k : ℝ)) ^ (2 * t - 2)) <
        (RamseyNumber s k : ℝ) := hhalf.trans_lt hRlarge
    have hbtarget : 2 * t - 2 = 2 * s - 4 := by
      dsimp [t]
      omega
    have hratioPos : 0 ≤ (k : ℝ) ^ t /
        (Real.log (k : ℝ)) ^ (2 * s - 4) := by
      positivity
    have hcB : c ≤ B / 2 := by
      dsimp [c]
      exact min_le_left _ _
    have hcle : c * ((k : ℝ) ^ t /
        (Real.log (k : ℝ)) ^ (2 * s - 4)) ≤
        B / 2 * ((k : ℝ) ^ t /
          (Real.log (k : ℝ)) ^ (2 * s - 4)) := by
      exact mul_le_mul_of_nonneg_right hcB hratioPos
    have hlargefinal' : B / 2 * ((k : ℝ) ^ t /
        (Real.log (k : ℝ)) ^ (2 * s - 4)) <
        (RamseyNumber s k : ℝ) := by
      simpa [hbtarget] using hlargefinal
    have hcle' : c * (k : ℝ) ^ (s - 1) /
        (Real.log (k : ℝ)) ^ (2 * s - 4) ≤
        B / 2 * ((k : ℝ) ^ t /
          (Real.log (k : ℝ)) ^ (2 * s - 4)) := by
      calc
        c * (k : ℝ) ^ (s - 1) /
            (Real.log (k : ℝ)) ^ (2 * s - 4) =
            c * ((k : ℝ) ^ t /
              (Real.log (k : ℝ)) ^ (2 * s - 4)) := by
                dsimp [t]
                ring
        _ ≤ B / 2 * ((k : ℝ) ^ t /
            (Real.log (k : ℝ)) ^ (2 * s - 4)) := hcle
    exact le_of_lt (lt_of_le_of_lt hcle' hlargefinal')
  · have hkN : k < N := by omega
    have hkN1 : k ≤ N + 1 := by omega
    have hRnat : 0 < RamseyNumber s k :=
      FiniteRamseyPositivity s k (by omega) (by omega)
    have hRoneNat : 1 ≤ RamseyNumber s k := by omega
    have hRone : (1 : ℝ) ≤ (RamseyNumber s k : ℝ) := by
      exact_mod_cast hRoneNat
    have hkreal1 : (1 : ℝ) < (k : ℝ) := by
      exact_mod_cast (show 1 < k by omega)
    have hlogpos : 0 < Real.log (k : ℝ) := Real.log_pos hkreal1
    have hlogmon : Real.log 2 ≤ Real.log (k : ℝ) := by
      apply Real.log_le_log (by norm_num)
      exact_mod_cast hk
    have hbase : (1 : ℝ) ≤ 2 * Real.log (k : ℝ) := by
      nlinarith [hlogtwo, hlogmon]
    have hbasepow : (1 : ℝ) ≤
        (2 * Real.log (k : ℝ)) ^ (2 * t - 2) := by
      exact one_le_pow₀ hbase
    have hfactor : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * t - 2) *
        (Real.log (k : ℝ)) ^ (2 * t - 2) := by
      simpa [mul_pow] using hbasepow
    have hkpow : (k : ℝ) ^ t ≤ (N + 1 : ℝ) ^ t := by
      exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hkN1) t
    have hdenpos : 0 < (Real.log (k : ℝ)) ^ (2 * s - 4) := by
      positivity
    have hbtarget : 2 * t - 2 = 2 * s - 4 := by
      dsimp [t]
      omega
    have hnum : (k : ℝ) ^ t ≤ M *
        (Real.log (k : ℝ)) ^ (2 * s - 4) := by
      calc
        (k : ℝ) ^ t ≤ (N + 1 : ℝ) ^ t := hkpow
        _ ≤ ((2 : ℝ) ^ (2 * t - 2) *
            (Real.log (k : ℝ)) ^ (2 * t - 2)) * (N + 1 : ℝ) ^ t := by
          have hh := mul_le_mul_of_nonneg_right hfactor
            (by positivity : (0 : ℝ) ≤ (N + 1 : ℝ) ^ t)
          simpa using hh
        _ = M * (Real.log (k : ℝ)) ^ (2 * s - 4) := by
          dsimp [M]
          rw [hbtarget]
          ring
    have hratio : (k : ℝ) ^ t /
        (Real.log (k : ℝ)) ^ (2 * s - 4) ≤ M := by
      apply (div_le_iff₀ hdenpos).2
      simpa [mul_comm] using hnum
    have hcM : c ≤ 1 / M := by
      dsimp [c]
      exact min_le_right _ _
    have hratioNonneg : 0 ≤ (k : ℝ) ^ t /
        (Real.log (k : ℝ)) ^ (2 * s - 4) := by positivity
    have hcm : c * ((k : ℝ) ^ t /
        (Real.log (k : ℝ)) ^ (2 * s - 4)) ≤ 1 := by
      calc
        c * ((k : ℝ) ^ t /
            (Real.log (k : ℝ)) ^ (2 * s - 4)) ≤
            (1 / M) * ((k : ℝ) ^ t /
              (Real.log (k : ℝ)) ^ (2 * s - 4)) :=
          mul_le_mul_of_nonneg_right hcM hratioNonneg
        _ = ((k : ℝ) ^ t /
            (Real.log (k : ℝ)) ^ (2 * s - 4)) / M := by ring
        _ ≤ 1 := by
          apply (div_le_iff₀ hM).2
          simpa using hratio
    have hcm' : c * (k : ℝ) ^ (s - 1) /
        (Real.log (k : ℝ)) ^ (2 * s - 4) ≤ 1 := by
      calc
        c * (k : ℝ) ^ (s - 1) /
            (Real.log (k : ℝ)) ^ (2 * s - 4) =
            c * ((k : ℝ) ^ t /
              (Real.log (k : ℝ)) ^ (2 * s - 4)) := by
                dsimp [t]
                ring
        _ ≤ 1 := hcm
    exact hcm'.trans hRone
