import Tablet.F2ForwardIndependentBound
import Tablet.F2AsymptoticCorollary
import Tablet.RandomPermutationReduction
import Tablet.SamplingDeletion

set_option maxHeartbeats 800000

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
  intro s a hs ha
  obtain ⟨e, he, hsum⟩ := F2AsymptoticCorollary s a hs ha
  have hroot_pow (E : ℝ) (K : Nat) (hK : 0 < K) :
      ((2 : ℝ) ^ (-E / (K : ℝ))) ^ K = (2 : ℝ) ^ (-E) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    field_simp
  have hprod_id (E : ℝ) (K : Nat) (hK : 0 < K) :
      (((K : ℝ) / Real.exp 1 * (2 : ℝ) ^ (-E / (K : ℝ))) ^ K) *
        (((Real.exp 1 / (K : ℝ)) ^ K) * (2 : ℝ) ^ E) = 1 := by
    have hK0 : (K : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hK)
    have he0 : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
    rw [mul_pow, hroot_pow E K hK]
    have hrat : ((K : ℝ) / Real.exp 1) ^ K *
        (Real.exp 1 / (K : ℝ)) ^ K = 1 := by
      rw [← mul_pow]
      field_simp
      ring
    have htwo : (2 : ℝ) ^ (-E) * (2 : ℝ) ^ E = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      ring_nf
      simp
    calc
      ((K : ℝ) / Real.exp 1) ^ K * (2 : ℝ) ^ (-E) *
          ((Real.exp 1 / (K : ℝ)) ^ K * (2 : ℝ) ^ E) =
          (((K : ℝ) / Real.exp 1) ^ K *
            (Real.exp 1 / (K : ℝ)) ^ K) *
            ((2 : ℝ) ^ (-E) * (2 : ℝ) ^ E) := by ring
      _ = 1 := by rw [hrat, htwo]; ring
  have hnegpow (δ : ℝ) (hδ : 0 ≤ δ) :
      1 - δ ≤ (2 : ℝ) ^ (-δ) := by
    have hlog0 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hlog0
    have hmul : δ * Real.log 2 ≤ δ := by
      nlinarith [mul_le_mul_of_nonneg_left hlog0 hδ]
    have h := Real.add_one_le_exp (-δ * Real.log 2)
    calc
      1 - δ ≤ 1 - δ * Real.log 2 := by linarith
      _ ≤ Real.exp (-δ * Real.log 2) := by linarith
      _ = (2 : ℝ) ^ (-δ) := by
        rw [Real.rpow_def_of_pos (by norm_num)]
        congr 1
        ring
  have hpower_loss (S : Nat) (δ : ℝ) (hS : 4 ≤ S) (hδ : 0 < δ)
      (hpow : 2 / δ ≤ (2 : ℝ) ^ S) :
      (1 - δ) * (2 : ℝ) ^ (2 * S - 3) ≤
        ((2 ^ (2 * S - 3) - 2 ^ (S - 2) : Nat) : ℝ) := by
    have hS1 : 1 ≤ S := by omega
    have hsplit : (2 : ℝ) ^ S = 2 * (2 : ℝ) ^ (S - 1) := by
      calc
        (2 : ℝ) ^ S = (2 : ℝ) ^ ((S - 1) + 1) := by congr 1 <;> omega
        _ = (2 : ℝ) ^ (S - 1) * 2 := by rw [pow_add, pow_one]
        _ = 2 * (2 : ℝ) ^ (S - 1) := by ring
    have hratio : 1 / δ ≤ (2 : ℝ) ^ (S - 1) := by
      have h := hpow
      rw [hsplit] at h
      have hdiv : 2 / δ = 2 * (1 / δ) := by ring
      rw [hdiv] at h
      nlinarith
    have hprod : 1 ≤ δ * (2 : ℝ) ^ (S - 1) := by
      have hmul := mul_le_mul_of_nonneg_left hratio (le_of_lt hδ)
      calc
        1 = δ * (1 / δ) := by field_simp
        _ ≤ δ * (2 : ℝ) ^ (S - 1) := hmul
    have hpowle : (2 : ℝ) ^ (S - 2) ≤
        (2 : ℝ) ^ (2 * S - 3) := by
      rw [show 2 * S - 3 = (S - 2) + (S - 1) by omega, pow_add]
      have hp : 0 ≤ (2 : ℝ) ^ (S - 2) := by positivity
      have hb : 1 ≤ (2 : ℝ) ^ (S - 1) := one_le_pow₀ (by norm_num)
      calc
        (2 : ℝ) ^ (S - 2) = (2 : ℝ) ^ (S - 2) * 1 := by ring
        _ ≤ (2 : ℝ) ^ (S - 2) * (2 : ℝ) ^ (S - 1) :=
          mul_le_mul_of_nonneg_left hb hp
    have hsmall : (2 : ℝ) ^ (S - 2) ≤
        δ * (2 : ℝ) ^ (2 * S - 3) := by
      have h := mul_le_mul_of_nonneg_left hprod
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (S - 2))
      have hexp : 2 * S - 3 = (S - 2) + (S - 1) := by omega
      calc
        (2 : ℝ) ^ (S - 2) = (2 : ℝ) ^ (S - 2) * 1 := by ring
        _ ≤ (2 : ℝ) ^ (S - 2) * (δ * (2 : ℝ) ^ (S - 1)) := h
        _ = δ * (2 : ℝ) ^ (2 * S - 3) := by
          rw [hexp, pow_add]
          ring
    have hcast : ((2 ^ (2 * S - 3) - 2 ^ (S - 2) : Nat) : ℝ) =
        (2 : ℝ) ^ (2 * S - 3) - (2 : ℝ) ^ (S - 2) := by
      rw [Nat.cast_sub (by exact_mod_cast hpowle)]
      norm_num [Nat.cast_pow]
    rw [hcast]
    nlinarith [hsmall]
  have hTnonneg (S A : Nat) (hS : 4 ≤ S) (hA : A ≤ S) :
      0 ≤ ((S + A - 1 : Nat) : ℝ) / 2 -
        (A : ℝ) ^ 2 / (2 * (S : ℝ)) := by
    have hSpos : (0 : ℝ) < S := by
      exact_mod_cast (show 0 < S by omega)
    have hA0 : (0 : ℝ) ≤ A := by positivity
    have hAS : (A : ℝ) ≤ S := by exact_mod_cast hA
    rw [Nat.cast_sub (by omega : 1 ≤ S + A), Nat.cast_one]
    push_cast
    have h1 : (0 : ℝ) ≤ S * (S - 1) := by
      have hSr : (4 : ℝ) ≤ S := by exact_mod_cast hS
      nlinarith
    have h2 : (0 : ℝ) ≤ A * (S - A) :=
      mul_nonneg hA0 (sub_nonneg.mpr hAS)
    field_simp
    nlinarith
  have hzero_bound (S A : Nat) (ε : ℝ) (hS : 8 ≤ S) (hA : A ≤ S)
      (hε : 0 < ε) (hε1 : ε < 1) :
      ((S : ℝ) / Real.exp 1) *
          Real.rpow 2 (((S + A - 1 : Nat) : ℝ) / 2 -
            (A : ℝ)^2 / (2 * (S : ℝ))) + 1 ≤
        (1 - ε / 8) * (2 : ℝ) ^ (2 * S - 3) := by
    have hSreal : (8 : ℝ) ≤ S := by exact_mod_cast hS
    have hA0 : (0 : ℝ) ≤ A := by positivity
    have hAS : (A : ℝ) ≤ S := by exact_mod_cast hA
    have hT0 := hTnonneg S A (by omega) hA
    have hTle : ((S + A - 1 : Nat) : ℝ) / 2 -
        (A : ℝ)^2 / (2 * (S : ℝ)) ≤ S := by
      rw [Nat.cast_sub (by omega : 1 ≤ S + A), Nat.cast_one]
      push_cast
      have h := sq_nonneg ((A : ℝ) - S)
      field_simp
      nlinarith
    have hpowT : Real.rpow 2 (((S + A - 1 : Nat) : ℝ) / 2 -
        (A : ℝ)^2 / (2 * (S : ℝ))) ≤ (2 : ℝ) ^ S := by
      calc
        _ ≤ Real.rpow 2 (S : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hTle
        _ = (2 : ℝ)^S := Real.rpow_natCast _ _
    have hSexp0 : ∀ m : Nat, 8 ≤ m → m ≤ 2 ^ (m - 4) := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => norm_num
      | succ n hn ih =>
          rw [show n + 1 - 4 = (n - 4) + 1 by omega, pow_succ]
          have hp : 1 ≤ 2 ^ (n - 4) := Nat.one_le_pow _ _ (by omega)
          nlinarith
    have hSexp : S ≤ 2 ^ (S - 4) := hSexp0 S hS
    have he2 : (2 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp (1 : ℝ)
      norm_num at h ⊢
      exact h
    have hcoef : (7 / 8 : ℝ) ≤ 1 - ε / 8 := by linarith
    have hSdiv : (S : ℝ) / Real.exp 1 ≤ (2 : ℝ) ^ (S - 5) := by
      have hSr : (S : ℝ) ≤ (2 : ℝ) ^ (S - 4) := by exact_mod_cast hSexp
      have hepos : 0 < Real.exp 1 := Real.exp_pos _
      have hhalf : (S : ℝ) / 2 ≤ (2 : ℝ) ^ (S - 5) := by
        have hpow : (2 : ℝ) ^ (S - 4) = 2 * (2 : ℝ) ^ (S - 5) := by
          calc
            (2 : ℝ) ^ (S - 4) = (2 : ℝ) ^ ((S - 5) + 1) := by congr 1 <;> omega
            _ = 2 * (2 : ℝ) ^ (S - 5) := by rw [pow_add, pow_one]; ring
        rw [hpow] at hSr
        nlinarith
      apply (div_le_iff₀ hepos).2
      nlinarith
    have hprod : ((S : ℝ) / Real.exp 1) * (2 : ℝ)^S ≤
        (2 : ℝ) ^ (2*S - 5) := by
      have hpow : (2 : ℝ) ^ (S - 5) * (2 : ℝ)^S =
          (2 : ℝ)^(2*S - 5) := by
        rw [← pow_add]
        congr 1
        omega
      calc
        _ ≤ (2 : ℝ)^(S-5) * (2 : ℝ)^S :=
          mul_le_mul_of_nonneg_right hSdiv (by positivity)
        _ = _ := hpow
    have hbig : (2 : ℝ) ^ (2*S - 5) + 1 ≤
        (1 - ε/8) * (2 : ℝ) ^ (2*S - 3) := by
      have hpow : (2 : ℝ) ^ (2*S - 3) = 4 * (2 : ℝ)^(2*S-5) := by
        calc
          _ = (2 : ℝ)^((2*S-5)+2) := by congr 1 <;> omega
          _ = _ := by rw [pow_add]; norm_num; ring
      rw [hpow]
      have hq : 1 ≤ (2 : ℝ)^(2*S-5) := one_le_pow₀ (by norm_num)
      nlinarith
    calc
      _ ≤ ((S : ℝ) / Real.exp 1) * (2 : ℝ)^S + 1 := by
        have hnon : 0 ≤ (S : ℝ) / Real.exp 1 := by positivity
        have hpow0 : 0 ≤ Real.rpow 2 (((S + A - 1 : Nat) : ℝ) / 2 -
            (A : ℝ)^2 / (2 * (S : ℝ))) := Real.rpow_nonneg (by norm_num) _
        nlinarith
      _ ≤ (2 : ℝ) ^ (2*S - 5) + 1 := by
        simpa [add_comm] using (add_le_add_right hprod 1)
      _ ≤ _ := hbig
  intro ε hε
  by_cases hεbig : 1 ≤ ε
  · filter_upwards [] with n
    have hbase0 : 0 ≤ ((s n : ℝ) / Real.exp 1) *
        Real.rpow 2 (((s n : ℝ) + (a n : ℝ) - 1) / 2 -
          (a n : ℝ)^2 / (2 * (s n : ℝ))) := by
      exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)
        (Real.rpow_nonneg (by norm_num) _)
    have hright : (1 - ε) * ((s n : ℝ) / Real.exp 1) *
        Real.rpow 2 (((s n : ℝ) + (a n : ℝ) - 1) / 2 -
          (a n : ℝ)^2 / (2 * (s n : ℝ))) ≤ 0 := by
      have hcoef : 1 - ε ≤ 0 := by linarith
      have h := mul_nonpos_of_nonpos_of_nonneg hcoef hbase0
      simpa [mul_assoc] using h
    have hR : (0 : ℝ) ≤ RamseyNumber (s n) (s n + a n) := Nat.cast_nonneg _
    linarith
  · have hεlt : ε < 1 := lt_of_not_ge hεbig
    have hδ : 0 < ε / 8 := by positivity
    have hsR : Filter.Tendsto (fun n => (s n : ℝ))
        Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop.comp hs
    have hpowS' : Filter.Tendsto (fun n => (2 : ℝ) ^ (s n))
        Filter.atTop Filter.atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp hs
    have hNpow : ∀ᶠ n in Filter.atTop,
        2 / (ε / 8) ≤ (2 : ℝ) ^ (s n) :=
      hpowS'.eventually_ge_atTop _
    have hS4 : ∀ᶠ n in Filter.atTop, 4 ≤ s n :=
      hs.eventually_ge_atTop 4
    have hS8 : ∀ᶠ n in Filter.atTop, 8 ≤ s n :=
      hs.eventually_ge_atTop 8
    have hA1 : ∀ᶠ n in Filter.atTop, a n ≤ s n := by
      have hone : (0 : ℝ) < 1 := by norm_num
      filter_upwards [ha.def hone] with n hn
      have ha0 : (0 : ℝ) ≤ (a n : ℝ) := Nat.cast_nonneg _
      have hs0 : (0 : ℝ) ≤ (s n : ℝ) := Nat.cast_nonneg _
      have hn' : (a n : ℝ) ≤ (s n : ℝ) := by
        simpa only [Real.norm_eq_abs, abs_of_nonneg ha0, abs_of_nonneg hs0,
          one_mul] using hn
      exact_mod_cast hn'
    obtain ⟨M, hM⟩ := exists_nat_gt (Real.exp 1 * (4 / (3 * ε)))
    have hbaseevent : ∀ᶠ n in Filter.atTop,
        4 / (3 * ε) ≤ (s n : ℝ) / Real.exp 1 *
          Real.rpow 2 (((s n : ℝ) + (a n : ℝ) - 1) / 2 -
            (a n : ℝ)^2 / (2 * (s n : ℝ))) := by
      filter_upwards [hS4, hA1, hs.eventually_ge_atTop M] with n hnS hnA hnM
      have hnMR : (M : ℝ) ≤ (s n : ℝ) := by exact_mod_cast hnM
      have hMR : Real.exp 1 * (4 / (3 * ε)) ≤ (M : ℝ) := le_of_lt hM
      have hSR : Real.exp 1 * (4 / (3 * ε)) ≤ (s n : ℝ) := hMR.trans hnMR
      have hdiv : 4 / (3 * ε) ≤ (s n : ℝ) / Real.exp 1 := by
        apply (le_div_iff₀ (Real.exp_pos 1)).2
        simpa [mul_comm] using hSR
      have hT := hTnonneg (s n) (a n) hnS hnA
      have hpowT := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hT
      have hcastSA : ((s n + a n - 1 : Nat) : ℝ) =
          (s n : ℝ) + (a n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ s n + a n), Nat.cast_one]
        push_cast
        ring
      have hpowT0 : (1 : ℝ) ≤ Real.rpow 2 (((s n : ℝ) + (a n : ℝ) - 1) / 2 -
          (a n : ℝ)^2 / (2 * (s n : ℝ))) := by
        rw [← hcastSA]
        norm_num at hpowT ⊢
        exact hpowT
      have hdiv0 : 0 ≤ (s n : ℝ) / Real.exp 1 := by positivity
      calc
        4 / (3 * ε) ≤ (s n : ℝ) / Real.exp 1 := hdiv
        _ = ((s n : ℝ) / Real.exp 1) * 1 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hpowT0 hdiv0
    have hha : ∀ᶠ n in Filter.atTop,
        ‖(a n : ℝ)‖ ≤ (ε / 40) * ‖(s n : ℝ)‖ := ha.def (by positivity)
    have hhe : ∀ᶠ n in Filter.atTop,
        ‖e n‖ ≤ (ε / 40) * ‖(s n : ℝ)‖ := he.def (by positivity)
    filter_upwards [hS4, hS8, hA1, hNpow, hbaseevent, hha, hhe, hsum] with n hnS hnS8 hnA hnN hnBase hna hne hhsum
    let S : Nat := s n
    let A : Nat := a n
    let K : Nat := S + A
    have hS4' : 4 ≤ S := by simpa [S] using hnS
    have hS8' : 8 ≤ S := by simpa [S] using hnS8
    have hA' : A ≤ S := by simpa [S, A] using hnA
    have hSK : S ≤ K := by dsimp [K]; omega
    have hKpos : 0 < K := by dsimp [K]; omega
    have hKreal : (0 : ℝ) < K := by exact_mod_cast hKpos
    have hδpow : 2 / (ε / 8) ≤ (2 : ℝ) ^ S := by simpa [S] using hnN
    have hcardlower : (1 - ε / 8) * (2 : ℝ) ^ (2 * S - 3) ≤
        ((2 ^ (2 * S - 3) - 2 ^ (S - 2) : Nat) : ℝ) :=
      hpower_loss S (ε / 8) hS4' hδ hδpow
    obtain ⟨D, hD, hDfree, hDcard, hDfwi⟩ :=
      F2ForwardIndependentBound S K hS4' hSK
    obtain ⟨G, hGcard, hGloop, hGfree, hGind⟩ :=
      RandomPermutationReduction D S K hDfree (by omega)
    have hcardeq : (@Fintype.card G.vertex G.fintype : ℝ) =
        ((2 ^ (2 * S - 3) - 2 ^ (S - 2) : Nat) : ℝ) := by
      rw [hGcard, hDcard]
    let E : ℝ := 3 / 2 * (S : ℝ) ^ 2 + (A : ℝ) * (S : ℝ) -
      5 / 2 * (S : ℝ) + e n
    have hsumE :
        (∑ t ∈ Finset.Icc 1 (S - 1),
          (Nat.choose K t *
            2 ^ ((S - 1) * (t + K) - Nat.choose (t + 1) 2) : Nat) : ℝ) ≤
        Real.rpow 2 E := by
      simpa [E, S, A, K] using hhsum
    have hIupper : (IndependentSetCount G K : ℝ) ≤
        (Real.exp 1 / (K : ℝ)) ^ K * Real.rpow 2 E := by
      calc
        (IndependentSetCount G K : ℝ) ≤
            (Real.exp 1 / (K : ℝ)) ^ K *
              (ForwardIndependentCount D K : ℝ) := hGind
        _ ≤ (Real.exp 1 / (K : ℝ)) ^ K *
            (∑ t ∈ Finset.Icc 1 (S - 1),
              (Nat.choose K t *
                2 ^ ((S - 1) * (t + K) - Nat.choose (t + 1) 2) : Nat) : ℝ) := by
              gcongr
        _ ≤ _ := by
          gcongr
    let p : ℝ := (K : ℝ) / Real.exp 1 *
      Real.rpow 2 (-E / (K : ℝ))
    have hp0 : 0 ≤ p := by
      dsimp [p]
      positivity
    have hcount : p ^ K * (IndependentSetCount G K : ℝ) ≤ 1 := by
      calc
        p ^ K * (IndependentSetCount G K : ℝ) ≤
            p ^ K * ((Real.exp 1 / (K : ℝ)) ^ K * Real.rpow 2 E) := by
              gcongr
        _ = 1 := by
          simpa [p] using hprod_id E K hKpos
    have hcardfactor : (1 - ε / 8) * (2 : ℝ) ^ (2 * S - 3) ≤
        (@Fintype.card G.vertex G.fintype : ℝ) := hcardlower.trans_eq hcardeq.symm
    by_cases hIzero : IndependentSetCount G K = 0
    · have hsamp := SamplingDeletion G S K hGloop hGfree (by omega)
          1 (by norm_num) (by norm_num) (by simp [hIzero])
      have hzero := hzero_bound S A ε hS8' hA' hε hεlt
      have hzero' :
          ((S : ℝ) / Real.exp 1) *
              Real.rpow 2 (((S + A - 1 : Nat) : ℝ) / 2 -
                (A : ℝ)^2 / (2 * (S : ℝ))) + 1 ≤
            (@Fintype.card G.vertex G.fintype : ℝ) := hzero.trans hcardfactor
      have hbase0 : 0 ≤ ((S : ℝ) / Real.exp 1) *
          Real.rpow 2 (((S + A - 1 : Nat) : ℝ) / 2 -
            (A : ℝ)^2 / (2 * (S : ℝ))) := by
        exact mul_nonneg (by positivity) (Real.rpow_nonneg (by norm_num) _)
      have htarget0 : (1 - ε) * ((S : ℝ) / Real.exp 1) *
          Real.rpow 2 (((S + A - 1 : Nat) : ℝ) / 2 -
            (A : ℝ)^2 / (2 * (S : ℝ))) ≤
          ((S : ℝ) / Real.exp 1) *
            Real.rpow 2 (((S + A - 1 : Nat) : ℝ) / 2 -
              (A : ℝ)^2 / (2 * (S : ℝ))) := by
        have h := mul_le_mul_of_nonneg_right (show 1 - ε ≤ 1 by linarith) hbase0
        simpa [mul_assoc] using h
      have htarget : (1 - ε) * ((S : ℝ) / Real.exp 1) *
          Real.rpow 2 (((S + A - 1 : Nat) : ℝ) / 2 -
            (A : ℝ)^2 / (2 * (S : ℝ))) ≤
          (@Fintype.card G.vertex G.fintype : ℝ) - 1 := by
        linarith
      have hR : (RamseyNumber S K : ℝ) >
          1 * (@Fintype.card G.vertex G.fintype : ℝ) - 1 := by simpa using hsamp
      have hR' : (@Fintype.card G.vertex G.fintype : ℝ) - 1 ≤
          (RamseyNumber S K : ℝ) := by simpa using (le_of_lt hR)
      have hresult := htarget.trans hR'
      have hcastSA : ((S + A - 1 : Nat) : ℝ) =
          (S : ℝ) + (A : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ S + A), Nat.cast_one]
        push_cast
        ring
      rw [hcastSA] at hresult
      simpa [S, A, K, Nat.cast_add] using hresult
    · have hIpos : 0 < IndependentSetCount G K :=
        Nat.pos_of_ne_zero hIzero
      have hIone : (1 : ℝ) ≤ (IndependentSetCount G K : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hIzero)
      have hpPow : p ^ K ≤ 1 := by
        calc
          p ^ K = p ^ K * 1 := by ring
          _ ≤ p ^ K * (IndependentSetCount G K : ℝ) := by gcongr
          _ ≤ 1 := hcount
      have hp1 : p ≤ 1 := by
        by_contra hp
        have hpgt : 1 < p := lt_of_not_ge hp
        have hpowlt : 1 < p ^ K :=
          one_lt_pow₀ hpgt (Nat.ne_of_gt hKpos)
        linarith
      have hsamp := SamplingDeletion G S K hGloop hGfree (by omega)
          p hp0 hp1 hcount
      have hAr : (A : ℝ) ≤ (ε / 40) * (S : ℝ) := by
        have hA0 : (0 : ℝ) ≤ A := by positivity
        have hS0 : (0 : ℝ) ≤ S := by positivity
        simpa [S, A, Real.norm_eq_abs, abs_of_nonneg hA0, abs_of_nonneg hS0] using hna
      have her : e n ≤ (ε / 40) * (S : ℝ) := by
        have heabs : |e n| ≤ (ε / 40) * (S : ℝ) := by
          simpa [S, Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ S by positivity)] using hne
        exact (le_abs_self _).trans heabs
      have hSKreal : (S : ℝ) ≤ (K : ℝ) := by exact_mod_cast hSK
      have hAK : (A : ℝ) / (K : ℝ) ≤ ε / 40 := by
        apply (div_le_iff₀ hKreal).2
        have hmul := mul_le_mul_of_nonneg_left hSKreal (by positivity : (0 : ℝ) ≤ ε / 40)
        exact hAr.trans hmul
      have hek : e n / (K : ℝ) ≤ ε / 40 := by
        apply (div_le_iff₀ hKreal).2
        have hmul := mul_le_mul_of_nonneg_left hSKreal (by positivity : (0 : ℝ) ≤ ε / 40)
        exact her.trans hmul
      let T : ℝ := ((S + A - 1 : Nat) : ℝ) / 2 -
        (A : ℝ)^2 / (2 * (S : ℝ))
      let P : ℝ := 2 * (S : ℝ) - 3 - E / (K : ℝ)
      have hPident : P = T - (A : ℝ) *
          (5 * (S : ℝ) - (A : ℝ)^2) / (2 * (S : ℝ) * (K : ℝ)) -
          e n / (K : ℝ) := by
        dsimp [P, T, E, K]
        rw [Nat.cast_sub (by omega : 1 ≤ S + A), Nat.cast_one]
        push_cast
        field_simp
        ring
      have hrough : - (A : ℝ) * (5 * (S : ℝ) - (A : ℝ)^2) /
          (2 * (S : ℝ) * (K : ℝ)) ≥ - 5 * (A : ℝ) / (2 * (K : ℝ)) := by
        have hSpos : (0 : ℝ) < S := by exact_mod_cast (show 0 < S by omega)
        have hA0 : (0 : ℝ) ≤ A := by positivity
        have hA3 : 0 ≤ (A : ℝ)^3 := by positivity
        field_simp
        nlinarith
      have hAterm : 5 * (A : ℝ) / (2 * (K : ℝ)) ≤ 5 * ε / 80 := by
        calc
          5 * (A : ℝ) / (2 * (K : ℝ)) = (5 / 2) * ((A : ℝ) / (K : ℝ)) := by
            field_simp
            -- field_simp closes this equality
          _ ≤ (5 / 2) * (ε / 40) := by gcongr
          _ = 5 * ε / 80 := by ring
      have herr : 5 * (A : ℝ) / (2 * (K : ℝ)) + e n / (K : ℝ) ≤ ε / 8 := by
        linarith [hAterm, hek]
      have hPbound : T - ε / 8 ≤ P := by
        have hprough : T - 5 * (A : ℝ) / (2 * (K : ℝ)) -
            e n / (K : ℝ) ≤ P := by
          calc
            T - 5 * (A : ℝ) / (2 * (K : ℝ)) - e n / (K : ℝ) ≤
                T - (A : ℝ) * (5 * (S : ℝ) - (A : ℝ)^2) /
                    (2 * (S : ℝ) * (K : ℝ)) - e n / (K : ℝ) := by
              have hh := add_le_add_right hrough (T - e n / (K : ℝ))
              calc
                _ = (-5 * (A : ℝ) / (2 * (K : ℝ))) +
                    (T - e n / (K : ℝ)) := by ring
                _ ≤ (-(A : ℝ) * (5 * (S : ℝ) - (A : ℝ)^2) /
                    (2 * (S : ℝ) * (K : ℝ))) +
                    (T - e n / (K : ℝ)) := by
                      simpa [add_comm, add_left_comm, add_assoc] using hh
                _ = _ := by ring
            _ = P := hPident.symm
        linarith [herr, hprough]
      have hpowP : Real.rpow 2 (T - ε / 8) ≤ Real.rpow 2 P :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hPbound
      have hfactor : 1 - ε / 8 ≤ Real.rpow 2 (-(ε / 8)) :=
        hnegpow (ε / 8) (le_of_lt hδ)
      have hpowlower : (1 - ε / 8) * Real.rpow 2 T ≤ Real.rpow 2 P := by
        calc
          (1 - ε / 8) * Real.rpow 2 T ≤
              Real.rpow 2 (-(ε / 8)) * Real.rpow 2 T := by
                have hTpow : 0 ≤ Real.rpow 2 T := Real.rpow_nonneg (by norm_num) _
                exact mul_le_mul_of_nonneg_right hfactor hTpow
          _ = Real.rpow 2 (T - ε / 8) := by
                calc
                  Real.rpow 2 (-(ε / 8)) * Real.rpow 2 T =
                      (2 : ℝ) ^ (-(ε / 8)) * (2 : ℝ) ^ T := rfl
                  _ = (2 : ℝ) ^ (-(ε / 8) + T) :=
                    (Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _).symm
                  _ = Real.rpow 2 (T - ε / 8) := by congr 1 <;> ring
          _ ≤ _ := hpowP
      have hcombine : Real.rpow 2 (-E / (K : ℝ)) *
          (2 : ℝ) ^ (2 * S - 3) = Real.rpow 2 P := by
        have hcast23 : ((2 * S - 3 : Nat) : ℝ) = 2 * (S : ℝ) - 3 := by
          rw [Nat.cast_sub (by omega : 3 ≤ 2 * S)]
          push_cast
          ring
        calc
          _ = Real.rpow 2 (-E / (K : ℝ)) *
              Real.rpow 2 ((2 * S - 3 : Nat) : ℝ) := by
                congr 1
                exact (Real.rpow_natCast (2 : ℝ) (2 * S - 3)).symm
          _ = Real.rpow 2 (-E / (K : ℝ) + ((2 * S - 3 : Nat) : ℝ)) := by
                exact (Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _).symm
          _ = Real.rpow 2 P := by
                congr 1
                rw [hcast23]
                dsimp [P]
                ring
      have hpcard : (1 - ε / 8) * (K : ℝ) / Real.exp 1 *
          Real.rpow 2 P ≤ p * (@Fintype.card G.vertex G.fintype : ℝ) := by
        calc
          (1 - ε / 8) * (K : ℝ) / Real.exp 1 * Real.rpow 2 P =
              p * ((1 - ε / 8) * (2 : ℝ) ^ (2 * S - 3)) := by
                dsimp [p]
                calc
                  (1 - ε / 8) * (K : ℝ) / Real.exp 1 * Real.rpow 2 P =
                      (K : ℝ) / Real.exp 1 * (1 - ε / 8) *
                        (Real.rpow 2 (-E / (K : ℝ)) *
                          (2 : ℝ) ^ (2 * S - 3)) := by
                    rw [hcombine]
                    ring
                  _ = p * ((1 - ε / 8) * (2 : ℝ) ^ (2 * S - 3)) := by
                    dsimp [p]
                    ring
          _ ≤ p * (@Fintype.card G.vertex G.fintype : ℝ) :=
            mul_le_mul_of_nonneg_left hcardfactor hp0
      have hKdiv : (S : ℝ) / Real.exp 1 ≤ (K : ℝ) / Real.exp 1 := by
        apply (div_le_div_iff₀ (Real.exp_pos 1) (Real.exp_pos 1)).2
        exact mul_le_mul_of_nonneg_right hSKreal (Real.exp_pos 1).le
      have hinner : (1 - ε / 8) * ((S : ℝ) / Real.exp 1) *
          Real.rpow 2 T ≤ (K : ℝ) / Real.exp 1 * Real.rpow 2 P := by
        calc
          (1 - ε / 8) * ((S : ℝ) / Real.exp 1) * Real.rpow 2 T ≤
              ((S : ℝ) / Real.exp 1) * Real.rpow 2 P := by
                have h := mul_le_mul_of_nonneg_left hpowlower
                  (by positivity : (0 : ℝ) ≤ (S : ℝ) / Real.exp 1)
                simpa [mul_assoc, mul_left_comm, mul_comm] using h
          _ ≤ (K : ℝ) / Real.exp 1 * Real.rpow 2 P :=
            mul_le_mul_of_nonneg_right hKdiv (Real.rpow_nonneg (by norm_num) _)
      have hmain : (1 - ε / 4) * ((S : ℝ) / Real.exp 1) *
          Real.rpow 2 T ≤ p * (@Fintype.card G.vertex G.fintype : ℝ) := by
        have hcoef : 1 - ε / 4 ≤ (1 - ε / 8) * (1 - ε / 8) := by
          nlinarith [sq_nonneg (ε / 8)]
        have hbase0 : 0 ≤ ((S : ℝ) / Real.exp 1) * Real.rpow 2 T := by
          exact mul_nonneg (by positivity) (Real.rpow_nonneg (by norm_num) _)
        have hcoefmul := mul_le_mul_of_nonneg_right hcoef hbase0
        calc
          (1 - ε / 4) * ((S : ℝ) / Real.exp 1) * Real.rpow 2 T ≤
              (1 - ε / 8) * (1 - ε / 8) *
                ((S : ℝ) / Real.exp 1) * Real.rpow 2 T := by
                  simpa [mul_assoc] using hcoefmul
          _ = (1 - ε / 8) * ((1 - ε / 8) *
                ((S : ℝ) / Real.exp 1) * Real.rpow 2 T) := by ring
          _ ≤ (1 - ε / 8) * ((K : ℝ) / Real.exp 1 * Real.rpow 2 P) := by
                have hδ0 : 0 ≤ 1 - ε / 8 := by linarith
                exact mul_le_mul_of_nonneg_left hinner hδ0
          _ ≤ _ := by
                convert hpcard using 1 <;> ring
      have hmargin : 1 ≤ (3 * ε / 4) *
          (((S : ℝ) / Real.exp 1) * Real.rpow 2 T) := by
        have hb : 4 / (3 * ε) ≤
            (S : ℝ) / Real.exp 1 * Real.rpow 2 T := by
          change 4 / (3 * ε) ≤ (s n : ℝ) / Real.exp 1 *
            Real.rpow 2 (((s n + a n - 1 : Nat) : ℝ) / 2 -
              (a n : ℝ)^2 / (2 * (s n : ℝ)))
          have hcastSA : ((s n + a n - 1 : Nat) : ℝ) =
              (s n : ℝ) + (a n : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ s n + a n), Nat.cast_one]
            push_cast
            ring
          rw [hcastSA]
          exact hnBase
        have hm := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ 3 * ε / 4)
        calc
          1 = (3 * ε / 4) * (4 / (3 * ε)) := by field_simp
          _ ≤ (3 * ε / 4) * (((S : ℝ) / Real.exp 1) * Real.rpow 2 T) := by
            exact hm
      have hsamp' : (RamseyNumber S K : ℝ) >
          p * (@Fintype.card G.vertex G.fintype : ℝ) - 1 := by
        simpa using hsamp
      have htarget : (1 - ε) * ((S : ℝ) / Real.exp 1) * Real.rpow 2 T ≤
          p * (@Fintype.card G.vertex G.fintype : ℝ) - 1 := by
        linarith [hmain, hmargin]
      have hR : (RamseyNumber S K : ℝ) ≥
          (1 - ε) * ((S : ℝ) / Real.exp 1) * Real.rpow 2 T :=
        htarget.trans (le_of_lt hsamp')
      have hTfinal : T = ((S : ℝ) + (A : ℝ) - 1) / 2 -
          (A : ℝ)^2 / (2 * (S : ℝ)) := by
        dsimp [T]
        rw [Nat.cast_sub (by omega : 1 ≤ S + A), Nat.cast_one]
        push_cast
        ring
      rw [hTfinal] at hR
      simpa [S, A, K] using hR
