import Tablet.OldPolarityConstruction
import Tablet.RandomPermutationReduction
import Tablet.SamplingDeletion

set_option maxHeartbeats 2000000

-- [TABLET NODE: ThmOffDiagonalGeneral]
theorem ThmOffDiagonalGeneral :
    ∀ delta : ℝ, 0 < delta → ∃ L : Nat, 0 < L ∧
      ∀ s k : Nat, L ≤ s → L * s ≤ k →
        (RamseyNumber s k : ℝ) ≥
          Real.rpow ((k : ℝ) / (s : ℝ)) ((1 - delta) * (s : ℝ)) := by
-- BODY
  classical
  intro delta hdelta
  let delta0 : ℝ := min delta (1 / 20)
  have hdelta0 : 0 < delta0 := by
    dsimp [delta0]
    exact lt_min hdelta (by norm_num)
  have hdelta0le : delta0 ≤ delta := by
    exact min_le_left _ _
  obtain ⟨L0, hL0, hOld⟩ := OldPolarityConstruction delta0 hdelta0
  let a : ℝ := delta0 / 4
  let C : ℝ := 1600 / delta0 ^ 2
  let R : ℝ := max 256 (max (128 * Real.exp 1)
    (max (20 / delta) (Real.rpow C (4 / delta0))))
  let L : Nat := max L0 (Nat.ceil R + 4)
  refine ⟨L, by dsimp [L]; omega, ?_⟩
  intro s k hs hsk
  have hL4 : 4 ≤ L := by
    have hR : (256 : ℝ) ≤ R := by dsimp [R]; exact le_max_left _ _
    have hceil : (256 : ℝ) ≤ (Nat.ceil R : ℝ) := by
      exact hR.trans (Nat.le_ceil R)
    have : 256 ≤ Nat.ceil R := by exact_mod_cast hceil
    dsimp [L]
    omega
  have hL0 : L0 ≤ L := by dsimp [L]; omega
  have hs4 : 4 ≤ s := le_trans (by omega : 4 ≤ L) hs
  have hs3 : 3 ≤ s := by omega
  have hspos : 0 < s := by omega
  have hkpos : 0 < k := by
    have : 0 < L * s := by positivity
    omega
  have hs0 : L0 ≤ s := by dsimp [L] at hs ⊢; omega
  have hL0s : L0 * s ≤ k := by
    exact (Nat.mul_le_mul_right s hL0).trans hsk
  obtain ⟨q, hqpow, hqprime, hq16, hqle, hqle2, K, hfield, hfintype,
      hKcard, ht, hconcl⟩ := hOld s k hs0 hL0s
  rcases hconcl with ⟨htri, hDfree, hDcard, hDfwi⟩
  let G : LoopGraph := @PolarityGraph K hfield hfintype (s - 2) ht
  let D : LooplessDigraph := OldPairDigraph G
  have hDfree' : ¬ Nonempty (TransitiveTournament D s) := by
    simpa [D, G] using hDfree
  obtain ⟨G', hGcard, hGloop, hGfree, hGind⟩ :=
    RandomPermutationReduction D s k hDfree' (by omega)
  let x : ℝ := (k : ℝ) / (s : ℝ)
  have hsR : (0 : ℝ) < s := by exact_mod_cast hspos
  have hskR : (L : ℝ) * (s : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hsk
  have hxL : (L : ℝ) ≤ x := by
    dsimp [x]
    exact (le_div_iff₀ hsR).2 hskR
  have hRreal : R ≤ (L : ℝ) := by
    have hceil : R ≤ (Nat.ceil R : ℝ) := Nat.le_ceil R
    have hsum : (Nat.ceil R : ℝ) ≤ (L : ℝ) := by
      have hn : Nat.ceil R ≤ L := by dsimp [L]; omega
      exact_mod_cast hn
    exact hceil.trans hsum
  have hxR : R ≤ x := hRreal.trans hxL
  have h256R : (256 : ℝ) ≤ R := by dsimp [R]; exact le_max_left _ _
  have hx256 : (256 : ℝ) ≤ x := h256R.trans hxR
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx1
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have ha : 0 < a := by dsimp [a]; positivity
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hCpow : Real.rpow C (4 / delta0) ≤ x := by
    have hCR : Real.rpow C (4 / delta0) ≤ R := by
      dsimp [R]
      exact (le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _))
    exact hCR.trans hxR
  have hCpowx : C ≤ Real.rpow x a := by
    have hmono := Real.rpow_le_rpow
      (Real.rpow_nonneg hCpos.le _) hCpow ha.le
    calc
      C = Real.rpow C (1 : ℝ) := by simp
      _ = Real.rpow C ((4 / delta0) * a) := by
        congr 1
        dsimp [a]
        field_simp
      _ = (Real.rpow C (4 / delta0)) ^ a :=
        Real.rpow_mul hCpos.le _ _
      _ ≤ Real.rpow x a := hmono
  have hlogbound : Real.log x ≤ (4 / delta0) * Real.rpow x a := by
    have hlog := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hxpos a)
    rw [Real.log_rpow hxpos] at hlog
    have hlog' : a * Real.log x ≤ Real.rpow x a := by
      change a * Real.log x ≤ Real.rpow x a - 1 at hlog
      have hsub : Real.rpow x a - 1 ≤ Real.rpow x a := by linarith
      exact hlog.trans hsub
    have hdiv : Real.log x ≤ Real.rpow x a / a :=
      (le_div_iff₀ ha).2 (by simpa [mul_comm] using hlog')
    calc
      Real.log x ≤ Real.rpow x a / a := hdiv
      _ = (4 / delta0) * Real.rpow x a := by
        dsimp [a]
        field_simp
  have hqhalf : delta0 / 400 * x / Real.log x ≤ (q : ℝ) := by
    have hqhalf' :
        (delta0 / 200 * x / Real.log x) / 2 ≤ (q : ℝ) := by
      calc
        (delta0 / 200 * x / Real.log x) / 2 ≤ (2 * (q : ℝ)) / 2 := by
          exact div_le_div_of_nonneg_right hqle2 (by norm_num)
        _ = (q : ℝ) := by ring
    convert hqhalf' using 1 <;> ring
  have hr : 0 ≤ 1 - delta0 / 2 := by
    have : delta0 ≤ (1 / 20 : ℝ) := min_le_right _ _
    linarith
  have htargetlog :
      Real.rpow x (1 - delta0 / 2) * Real.log x ≤ delta0 / 400 * x := by
    have hrpowadd (u v : ℝ) : Real.rpow x u * Real.rpow x v =
        Real.rpow x (u + v) := (Real.rpow_add hxpos u v).symm
    have hleft : Real.rpow x (1 - delta0 / 2) * Real.log x ≤
        Real.rpow x (1 - delta0 / 2) *
          ((4 / delta0) * Real.rpow x a) :=
      mul_le_mul_of_nonneg_left hlogbound
        (Real.rpow_nonneg hxpos.le (1 - delta0 / 2))
    have hcoef : 4 / delta0 ≤ delta0 / 400 * Real.rpow x a := by
      calc
        4 / delta0 = (delta0 / 400) * C := by
          dsimp [C]
          field_simp
          ring
        _ ≤ (delta0 / 400) * Real.rpow x a := by
          exact mul_le_mul_of_nonneg_left hCpowx (by positivity)
    calc
      Real.rpow x (1 - delta0 / 2) * Real.log x ≤
          Real.rpow x (1 - delta0 / 2) *
            ((4 / delta0) * Real.rpow x a) := hleft
      _ = (4 / delta0) * Real.rpow x (1 - delta0 / 2 + a) := by
        calc
          Real.rpow x (1 - delta0 / 2) *
              (4 / delta0 * Real.rpow x a) =
              (4 / delta0) *
                (Real.rpow x (1 - delta0 / 2) * Real.rpow x a) := by ring
          _ = _ := by rw [hrpowadd]
      _ ≤ (delta0 / 400) * Real.rpow x (1 - delta0 / 2 + a) *
            Real.rpow x a := by
        have hmul := mul_le_mul_of_nonneg_right hcoef
          (Real.rpow_nonneg hxpos.le (1 - delta0 / 2 + a))
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      _ = delta0 / 400 * x := by
        calc
          delta0 / 400 * Real.rpow x (1 - delta0 / 2 + a) *
              Real.rpow x a = delta0 / 400 *
                (Real.rpow x (1 - delta0 / 2 + a) *
                  Real.rpow x a) := by ring
          _ = delta0 / 400 *
                Real.rpow x ((1 - delta0 / 2 + a) + a) := by
                  rw [hrpowadd]
          _ = delta0 / 400 * x := by
            congr 2
            dsimp [a]
            ring_nf
            simp [Real.rpow_one]
  have hqpowlower : Real.rpow x (1 - delta0 / 2) ≤ (q : ℝ) := by
    have hqdiv : Real.rpow x (1 - delta0 / 2) ≤
        delta0 / 400 * x / Real.log x :=
      (le_div_iff₀ hlogpos).2 htargetlog
    exact hqdiv.trans hqhalf
  let E : ℝ := 2 * ((s - 2 : Nat) : ℝ) -
    ((s - 3 : Nat) : ℝ) * (1 - delta0 / 5)
  have hDfwi' : (ForwardIndependentCount D k : ℝ) ≤
      (32 * Real.rpow (q : ℝ) E) ^ k := by
    simpa [E] using hDfwi
  have hIupper : (IndependentSetCount G' k : ℝ) ≤
      (Real.exp 1 / (k : ℝ)) ^ k *
        (32 * Real.rpow (q : ℝ) E) ^ k := by
    calc
      (IndependentSetCount G' k : ℝ) ≤
          (Real.exp 1 / (k : ℝ)) ^ k *
            (ForwardIndependentCount D k : ℝ) := hGind
      _ ≤ (Real.exp 1 / (k : ℝ)) ^ k *
          (32 * Real.rpow (q : ℝ) E) ^ k := by gcongr
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hEge : ((s - 1 : Nat) : ℝ) ≤ E := by
    dsimp [E]
    have hd0 : delta0 ≤ (1 / 20 : ℝ) := min_le_right _ _
    have hs3R : (0 : ℝ) ≤ (s - 3 : Nat) := by positivity
    have hs1cast : ((s - 1 : Nat) : ℝ) = (s : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ s)]
      norm_num
    have hs2cast : ((s - 2 : Nat) : ℝ) = (s : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ s)]
      norm_num
    have hs3cast : ((s - 3 : Nat) : ℝ) = (s : ℝ) - 3 := by
      rw [Nat.cast_sub (by omega : 3 ≤ s)]
      norm_num
    rw [hs1cast, hs2cast, hs3cast]
    nlinarith
  have hqpow_s : (s : ℝ) ≤ (q : ℝ) ^ (s - 3) := by
    have hnat : ∀ n : Nat, 4 ≤ n → n ≤ 16 ^ (n - 3) := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => norm_num
      | succ n hn ih =>
          rw [show n + 1 - 3 = (n - 3) + 1 by omega, pow_succ]
          have hmul : 16 * n ≤ 16 * (16 ^ (n - 3)) :=
            Nat.mul_le_mul_left 16 ih
          have hn16 : n + 1 ≤ 16 * n := by omega
          omega
    have hnat' : s ≤ 16 ^ (s - 3) := hnat s hs4
    have hq16R : (16 : ℝ) ≤ q := by exact_mod_cast hq16
    have hpow : (16 : ℝ) ^ (s - 3) ≤ (q : ℝ) ^ (s - 3) := by
      exact pow_le_pow_left₀ (by norm_num) hq16R _
    have hnatR : (s : ℝ) ≤ (16 : ℝ) ^ (s - 3) := by
      exact_mod_cast hnat'
    exact hnatR.trans hpow
  have hqpow_sq : x ≤ (q : ℝ) ^ 2 := by
    have hsq : Real.rpow x (1 - delta0 / 2) ^ 2 ≤ (q : ℝ) ^ 2 := by
      exact (sq_le_sq₀ (Real.rpow_nonneg hxpos.le (1 - delta0 / 2))
        (le_of_lt hqpos)).2 hqpowlower
    have hpowadd : Real.rpow x (1 - delta0 / 2) ^ 2 =
        Real.rpow x (2 * (1 - delta0 / 2)) := by
      calc
        Real.rpow x (1 - delta0 / 2) ^ 2 =
            (Real.rpow x (1 - delta0 / 2)) ^ (2 : ℝ) :=
              (Real.rpow_natCast _ _).symm
        _ = Real.rpow x ((1 - delta0 / 2) * 2) :=
          (Real.rpow_mul hxpos.le _ _).symm
        _ = _ := by congr 1 <;> ring
    have hexp : (1 : ℝ) ≤ 2 * (1 - delta0 / 2) := by
      have hd0 : delta0 ≤ (1 / 20 : ℝ) := min_le_right _ _
      linarith
    have hxe : x ≤ Real.rpow x (2 * (1 - delta0 / 2)) :=
      calc
        x = Real.rpow x (1 : ℝ) := by simp
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 hexp
    exact hxe.trans_eq hpowadd.symm |>.trans hsq
  have hqpow_sk : (k : ℝ) ≤ (q : ℝ) ^ (s - 1) := by
    have hksx : (k : ℝ) = (s : ℝ) * x := by
      dsimp [x]
      field_simp
    have hmul := mul_le_mul hqpow_s hqpow_sq (by positivity : (0 : ℝ) ≤ x)
      (by positivity : (0 : ℝ) ≤ (q : ℝ) ^ (s - 3))
    calc
      (k : ℝ) = (s : ℝ) * x := hksx
      _ ≤ (q : ℝ) ^ (s - 3) * (q : ℝ) ^ 2 := hmul
      _ = (q : ℝ) ^ (s - 1) := by
        rw [← pow_add]
        congr 1
        omega
  have hqpow_E : (k : ℝ) ≤ Real.rpow (q : ℝ) E := by
    have hpowexp : Real.rpow (q : ℝ) ((s - 1 : Nat) : ℝ) ≤
        Real.rpow (q : ℝ) E :=
      Real.rpow_le_rpow_of_exponent_le hqone hEge
    calc
      (k : ℝ) ≤ (q : ℝ) ^ (s - 1) := hqpow_sk
      _ = Real.rpow (q : ℝ) ((s - 1 : Nat) : ℝ) :=
        (Real.rpow_natCast _ _).symm
      _ ≤ _ := hpowexp
  let p : ℝ := (k : ℝ) / (32 * Real.exp 1) *
    Real.rpow (q : ℝ) (-E)
  have hp0 : 0 ≤ p := by
    dsimp [p]
    positivity
  have hqEpos : 0 < Real.rpow (q : ℝ) E :=
    Real.rpow_pos_of_pos hqpos E
  have hpform : p = ((k : ℝ) / Real.rpow (q : ℝ) E) /
      (32 * Real.exp 1) := by
    dsimp [p]
    rw [Real.rpow_neg hqpos.le]
    field_simp
  have hp1 : p ≤ 1 := by
    rw [hpform]
    have hratio : (k : ℝ) / Real.rpow (q : ℝ) E ≤ 1 := by
      apply (div_le_iff₀ hqEpos).2
      simpa using hqpow_E
    have hden : (1 : ℝ) ≤ 32 * Real.exp 1 := by
      have he : (1 : ℝ) ≤ Real.exp 1 := by
        have h := Real.add_one_le_exp (1 : ℝ)
        norm_num at h ⊢
      nlinarith
    calc
      (k : ℝ) / Real.rpow (q : ℝ) E / (32 * Real.exp 1) ≤
          1 / (32 * Real.exp 1) :=
        div_le_div_of_nonneg_right hratio (by positivity)
      _ ≤ 1 := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 32 * Real.exp 1)).2
        nlinarith
  have hpcancel : p * (Real.exp 1 / (k : ℝ)) *
      (32 * Real.rpow (q : ℝ) E) = 1 := by
    dsimp [p]
    rw [Real.rpow_neg hqpos.le]
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hkpos)
    field_simp [hk0, hqEpos.ne', Real.exp_ne_zero]
  have hcount : p ^ k * (IndependentSetCount G' k : ℝ) ≤ 1 := by
    calc
      p ^ k * (IndependentSetCount G' k : ℝ) ≤
          p ^ k * ((Real.exp 1 / (k : ℝ)) ^ k *
            (32 * Real.rpow (q : ℝ) E) ^ k) := by
              gcongr
      _ = (p * (Real.exp 1 / (k : ℝ)) *
          (32 * Real.rpow (q : ℝ) E)) ^ k := by
            calc
              p ^ k * ((Real.exp 1 / (k : ℝ)) ^ k *
                  (32 * Real.rpow (q : ℝ) E) ^ k) =
                  (p ^ k * (Real.exp 1 / (k : ℝ)) ^ k) *
                    (32 * Real.rpow (q : ℝ) E) ^ k := by ring
              _ = (p * (Real.exp 1 / (k : ℝ))) ^ k *
                    (32 * Real.rpow (q : ℝ) E) ^ k := by
                simp only [mul_pow]
              _ = (p * (Real.exp 1 / (k : ℝ)) *
                    (32 * Real.rpow (q : ℝ) E)) ^ k := by
                simp only [mul_pow]
      _ = 1 := by rw [hpcancel, one_pow]
  have hDcard' : Real.rpow (q : ℝ) ((2 * (s - 2) : Nat) : ℝ) / 2 ≤
      (@Fintype.card D.vertex D.fintype : ℝ) := by
    calc
      Real.rpow (q : ℝ) ((2 * (s - 2) : Nat) : ℝ) / 2 =
          (q : ℝ) ^ (2 * (s - 2)) / 2 := by
            exact congrArg (fun z : ℝ => z / 2)
              (Real.rpow_natCast (q : ℝ) (2 * (s - 2)))
      _ ≤ _ := by simpa [D, G] using hDcard
  have hGcardlower : Real.rpow (q : ℝ) ((2 * (s - 2) : Nat) : ℝ) / 2 ≤
      (@Fintype.card G'.vertex G'.fintype : ℝ) := by
    exact hDcard'.trans_eq (by simpa using hGcard.symm)
  let B : ℝ := ((s - 3 : Nat) : ℝ) * (1 - delta0 / 5)
  have hBnonneg : 0 ≤ B := by
    dsimp [B]
    have hd0 : delta0 ≤ (1 / 20 : ℝ) := min_le_right _ _
    have hs3R : (0 : ℝ) ≤ (s - 3 : Nat) := by positivity
    have hcoef : 0 ≤ 1 - delta0 / 5 := by linarith
    exact mul_nonneg hs3R hcoef
  have hqprod : Real.rpow (q : ℝ) (-E) *
      Real.rpow (q : ℝ) ((2 * (s - 2) : Nat) : ℝ) =
      Real.rpow (q : ℝ) B := by
    calc
      Real.rpow (q : ℝ) (-E) *
          Real.rpow (q : ℝ) ((2 * (s - 2) : Nat) : ℝ) =
          Real.rpow (q : ℝ) (-E + ((2 * (s - 2) : Nat) : ℝ)) :=
            (Real.rpow_add hqpos _ _).symm
      _ = Real.rpow (q : ℝ) B := by
        congr 1
        dsimp [B, E]
        have hs2cast : ((s - 2 : Nat) : ℝ) = (s : ℝ) - 2 := by
          rw [Nat.cast_sub (by omega : 2 ≤ s)]
          norm_num
        have hs3cast : ((s - 3 : Nat) : ℝ) = (s : ℝ) - 3 := by
          rw [Nat.cast_sub (by omega : 3 ≤ s)]
          norm_num
        have hcastprod : ((2 * (s - 2) : Nat) : ℝ) =
            2 * ((s - 2 : Nat) : ℝ) := by norm_num
        rw [hcastprod, hs2cast, hs3cast]
        ring
  have hpcardlower : (k : ℝ) / (64 * Real.exp 1) *
      Real.rpow (q : ℝ) B ≤
      p * (@Fintype.card G'.vertex G'.fintype : ℝ) := by
    have hpeq : (k : ℝ) / (64 * Real.exp 1) * Real.rpow (q : ℝ) B =
        p * (Real.rpow (q : ℝ) ((2 * (s - 2) : Nat) : ℝ) / 2) := by
      calc
        (k : ℝ) / (64 * Real.exp 1) * Real.rpow (q : ℝ) B =
            (k : ℝ) / (32 * Real.exp 1) *
              (Real.rpow (q : ℝ) B / 2) := by ring
        _ = (k : ℝ) / (32 * Real.exp 1) *
              (Real.rpow (q : ℝ) (-E) *
                Real.rpow (q : ℝ) ((2 * (s - 2) : Nat) : ℝ) / 2) := by
              rw [hqprod]
        _ = p * (Real.rpow (q : ℝ) ((2 * (s - 2) : Nat) : ℝ) / 2) := by
              dsimp [p]
              ring
    calc
      (k : ℝ) / (64 * Real.exp 1) * Real.rpow (q : ℝ) B =
          p * (Real.rpow (q : ℝ) ((2 * (s - 2) : Nat) : ℝ) / 2) := hpeq
      _ ≤ p * (@Fintype.card G'.vertex G'.fintype : ℝ) := by
        exact mul_le_mul_of_nonneg_left hGcardlower hp0
  have hqB : Real.rpow x ((1 - delta0 / 2) * B) ≤
      Real.rpow (q : ℝ) B := by
    have hbase := Real.rpow_le_rpow
      (Real.rpow_nonneg hxpos.le (1 - delta0 / 2)) hqpowlower hBnonneg
    calc
      Real.rpow x ((1 - delta0 / 2) * B) =
          (Real.rpow x (1 - delta0 / 2)) ^ B :=
            Real.rpow_mul hxpos.le _ _
      _ ≤ Real.rpow (q : ℝ) B := hbase
  let A : ℝ := 1 + (1 - delta0 / 2) * B
  have hbase_lower : (s : ℝ) / (64 * Real.exp 1) *
      Real.rpow x A ≤
      p * (@Fintype.card G'.vertex G'.fintype : ℝ) := by
    have hkx : (k : ℝ) = (s : ℝ) * x := by
      dsimp [x]
      field_simp
    have hqB' : Real.rpow x ((1 - delta0 / 2) * B) ≤
        Real.rpow (q : ℝ) B := hqB
    have hnonnegcoef : 0 ≤ (s : ℝ) / (64 * Real.exp 1) := by positivity
    calc
      (s : ℝ) / (64 * Real.exp 1) * Real.rpow x A =
          (k : ℝ) / (64 * Real.exp 1) *
            Real.rpow x ((1 - delta0 / 2) * B) := by
              dsimp [A]
              have hadd := Real.rpow_add hxpos
                (1 : ℝ) ((1 - delta0 / 2) * B)
              rw [Real.rpow_one] at hadd
              rw [hadd]
              rw [hkx]
              ring
      _ ≤ (k : ℝ) / (64 * Real.exp 1) *
          Real.rpow (q : ℝ) B := by
            exact mul_le_mul_of_nonneg_left hqB'
              (by positivity)
      _ ≤ p * (@Fintype.card G'.vertex G'.fintype : ℝ) := hpcardlower
  have h20s : 20 / delta ≤ (s : ℝ) := by
    have hRL : R ≤ (L : ℝ) := hRreal
    have hLs : (L : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    have h20R : 20 / delta ≤ R := by
      dsimp [R]
      calc
        20 / delta ≤ max (20 / delta) (Real.rpow C (4 / delta0)) :=
          le_max_left _ _
        _ ≤ max (128 * Real.exp 1)
              (max (20 / delta) (Real.rpow C (4 / delta0))) :=
          le_max_right _ _
        _ ≤ max 256
              (max (128 * Real.exp 1)
                (max (20 / delta) (Real.rpow C (4 / delta0)))) :=
          le_max_right _ _
    exact h20R.trans (hRL.trans hLs)
  have h128x : 128 * Real.exp 1 ≤ x := by
    have h128R : 128 * Real.exp 1 ≤ R := by
      dsimp [R]
      calc
        128 * Real.exp 1 ≤ max (128 * Real.exp 1)
              (max (20 / delta) (Real.rpow C (4 / delta0))) :=
          le_max_left _ _
        _ ≤ max 256
              (max (128 * Real.exp 1)
                (max (20 / delta) (Real.rpow C (4 / delta0)))) :=
          le_max_right _ _
    exact h128R.trans hxR
  have hsreal1 : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
  have hcoeff : (2 : ℝ) ≤ (s : ℝ) / (64 * Real.exp 1) * x := by
    have hden : (0 : ℝ) < 64 * Real.exp 1 := by positivity
    have hs128 : 128 * Real.exp 1 ≤
        (s : ℝ) * (128 * Real.exp 1) := by
      have := mul_le_mul_of_nonneg_right hsreal1 (by positivity : (0 : ℝ) ≤
        128 * Real.exp 1)
      nlinarith
    have hxs : (s : ℝ) * (128 * Real.exp 1) ≤ (s : ℝ) * x :=
      mul_le_mul_of_nonneg_left h128x (by positivity)
    have hcoeff' : (2 : ℝ) ≤ ((s : ℝ) * x) / (64 * Real.exp 1) := by
      apply (le_div_iff₀ hden).2
      convert hs128.trans hxs using 1 <;> ring
    calc
      (2 : ℝ) ≤ ((s : ℝ) * x) / (64 * Real.exp 1) := hcoeff'
      _ = (s : ℝ) / (64 * Real.exp 1) * x := by ring
  let beta : ℝ := (1 - delta0 / 2) * (1 - delta0 / 5)
  have hbeta : 1 - beta ≤ (7 / 10 : ℝ) * delta := by
    have hd0le : delta0 ≤ delta := hdelta0le
    have hd0small : delta0 ≤ (1 / 20 : ℝ) := min_le_right _ _
    dsimp [beta]
    nlinarith [sq_nonneg delta0]
  have hgap_eq : A - (1 - delta) * (s : ℝ) =
      delta * (s : ℝ) - ((s - 3 : Nat) : ℝ) * (1 - beta) - 2 := by
    dsimp [A, B, beta]
    have hs3cast : ((s - 3 : Nat) : ℝ) = (s : ℝ) - 3 := by
      rw [Nat.cast_sub (by omega : 3 ≤ s)]
      norm_num
    rw [hs3cast]
    ring
  have hgap : (1 : ℝ) ≤ A - (1 - delta) * (s : ℝ) := by
    have hs3nonneg : (0 : ℝ) ≤ ((s - 3 : Nat) : ℝ) := by positivity
    have hmulgap : ((s - 3 : Nat) : ℝ) * (1 - beta) ≤
        ((s - 3 : Nat) : ℝ) * ((7 / 10 : ℝ) * delta) :=
      mul_le_mul_of_nonneg_left hbeta hs3nonneg
    have hdelS : (20 : ℝ) ≤ delta * (s : ℝ) := by
      have := mul_le_mul_of_nonneg_left h20s (le_of_lt hdelta)
      field_simp at this ⊢
      nlinarith
    rw [hgap_eq]
    have hs3le : ((s - 3 : Nat) : ℝ) ≤ (s : ℝ) := by
      have : s - 3 ≤ s := by omega
      exact_mod_cast this
    nlinarith [mul_le_mul_of_nonneg_right hs3le
      (by positivity : (0 : ℝ) ≤ (7 / 10 : ℝ) * delta)]
  by_cases hdelta_lt : delta < 1
  · let T : ℝ := (1 - delta) * (s : ℝ)
    have hTA : T + 1 ≤ A := by
      dsimp [T]
      linarith [hgap]
    have hpowTA : Real.rpow x (T + 1) ≤ Real.rpow x A :=
      Real.rpow_le_rpow_of_exponent_le hx1 hTA
    have hpowaddT : Real.rpow x T * x = Real.rpow x (T + 1) := by
      calc
        Real.rpow x T * x = Real.rpow x T * Real.rpow x (1 : ℝ) := by
          simp
        _ = Real.rpow x (T + 1) := (Real.rpow_add hxpos _ _).symm
    have htargetnonneg : 0 ≤ Real.rpow x T :=
      Real.rpow_nonneg hxpos.le _
    have htwice : 2 * Real.rpow x T ≤
        (s : ℝ) / (64 * Real.exp 1) * Real.rpow x A := by
      calc
        2 * Real.rpow x T ≤
            ((s : ℝ) / (64 * Real.exp 1) * x) * Real.rpow x T := by
              exact mul_le_mul_of_nonneg_right hcoeff htargetnonneg
        _ = (s : ℝ) / (64 * Real.exp 1) *
              (x * Real.rpow x T) := by ring
        _ = (s : ℝ) / (64 * Real.exp 1) * Real.rpow x (T + 1) := by
              rw [mul_comm x, hpowaddT]
        _ ≤ (s : ℝ) / (64 * Real.exp 1) * Real.rpow x A := by
              exact mul_le_mul_of_nonneg_left hpowTA (by positivity)
    have honeT : (1 : ℝ) ≤ Real.rpow x T := by
      have hTnonneg : (0 : ℝ) ≤ T := by
        dsimp [T]
        exact mul_nonneg (sub_nonneg.mpr (le_of_lt hdelta_lt)) (by positivity)
      calc
        (1 : ℝ) = Real.rpow x 0 := by simp
        _ ≤ Real.rpow x T :=
          Real.rpow_le_rpow_of_exponent_le hx1 hTnonneg
    have hfinal : Real.rpow x T ≤
        p * (@Fintype.card G'.vertex G'.fintype : ℝ) - 1 := by
      linarith [hbase_lower, htwice, honeT]
    have hsamp := SamplingDeletion G' s k hGloop hGfree (by omega)
      p hp0 hp1 hcount
    have hsamp' : (RamseyNumber s k : ℝ) >
        p * (@Fintype.card G'.vertex G'.fintype : ℝ) - 1 := by
      simpa using hsamp
    have hRfinal : (RamseyNumber s k : ℝ) ≥ Real.rpow x T :=
      hfinal.trans (le_of_lt hsamp')
    simpa [x, T] using hRfinal
  · have hdelta_ge : 1 ≤ delta := le_of_not_gt hdelta_lt
    let T : ℝ := (1 - delta) * (s : ℝ)
    have hTnonpos : T ≤ 0 := by
      dsimp [T]
      nlinarith [show (0 : ℝ) ≤ s by positivity]
    have htargetone : Real.rpow x T ≤ 1 := by
      calc
        Real.rpow x T ≤ Real.rpow x 0 :=
          Real.rpow_le_rpow_of_exponent_le hx1 hTnonpos
        _ = 1 := by simp
    have hAone : (1 : ℝ) ≤ A := by
      dsimp [A]
      have hrB : 0 ≤ (1 - delta0 / 2) * B :=
        mul_nonneg hr hBnonneg
      linarith
    have hpowxA : x ≤ Real.rpow x A := by
      calc
        x = Real.rpow x (1 : ℝ) := by simp
        _ ≤ Real.rpow x A := Real.rpow_le_rpow_of_exponent_le hx1 hAone
    have htwofinal : (2 : ℝ) ≤
        p * (@Fintype.card G'.vertex G'.fintype : ℝ) := by
      calc
        (2 : ℝ) ≤ (s : ℝ) / (64 * Real.exp 1) * x := hcoeff
        _ ≤ (s : ℝ) / (64 * Real.exp 1) * Real.rpow x A := by
          exact mul_le_mul_of_nonneg_left hpowxA (by positivity)
        _ ≤ p * (@Fintype.card G'.vertex G'.fintype : ℝ) := hbase_lower
    have hfinal : Real.rpow x T ≤
        p * (@Fintype.card G'.vertex G'.fintype : ℝ) - 1 := by
      linarith
    have hsamp := SamplingDeletion G' s k hGloop hGfree (by omega)
      p hp0 hp1 hcount
    have hsamp' : (RamseyNumber s k : ℝ) >
        p * (@Fintype.card G'.vertex G'.fintype : ℝ) - 1 := by
      simpa using hsamp
    have hRfinal : (RamseyNumber s k : ℝ) ≥ Real.rpow x T :=
      hfinal.trans (le_of_lt hsamp')
    simpa [x, T] using hRfinal
