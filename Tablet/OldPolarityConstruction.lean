import Tablet.OldPairDigraph
import Tablet.OldPairDigraphProperties
import Tablet.OldPolarityParameters
import Tablet.OldCoherentTreeCount
import Tablet.AlonRodlBound
import Tablet.ExpanderMixing
import Tablet.ForwardIndependentTuple
import Tablet.ForwardIndependentCount
import Mathlib.FieldTheory.Cardinality

set_option maxHeartbeats 2000000
-- [TABLET NODE: OldPolarityConstruction]
theorem OldPolarityConstruction (delta : ℝ) (hdelta : 0 < delta) :
    ∃ L : Nat, 0 < L ∧ ∀ s k : Nat, L ≤ s → L * s ≤ k →
      ∃ q : Nat, (∃ m : Nat, q = 2 ^ m) ∧ IsPrimePow q ∧ 16 ≤ q ∧
        (q : ℝ) ≤ delta / 200 * ((k : ℝ) / (s : ℝ)) /
            Real.log ((k : ℝ) / (s : ℝ)) ∧
        delta / 200 * ((k : ℝ) / (s : ℝ)) /
            Real.log ((k : ℝ) / (s : ℝ)) ≤ 2 * q ∧
        ∃ K : Type, ∃ hfield : Field K, ∃ hfintype : Fintype K,
          @Fintype.card K hfintype = q ∧
          ∃ ht : 2 ≤ s - 2,
            let G := @PolarityGraph K hfield hfintype (s - 2) ht
            let D := OldPairDigraph G
            (∀ (a b : Fin s → G.vertex),
              (∀ i, ¬ G.adj (a i) (b i)) →
              (∀ ⦃i j : Fin s⦄, i.val < j.val → G.adj (a i) (b j)) → False) ∧
            ¬ Nonempty (TransitiveTournament D s) ∧
            ((q : ℝ) ^ (2 * (s - 2)) / 2 ≤
              (@Fintype.card D.vertex D.fintype : ℝ)) ∧
            (ForwardIndependentCount D k : ℝ) ≤
                  (32 * Real.rpow (q : ℝ)
                (2 * (s - 2 : Nat) - ((s - 3 : Nat) : ℝ) *
                  (1 - delta / 5))) ^ k := by
-- BODY
  classical
  have hlog_sqrt {x : ℝ} (hx : 1 ≤ x) :
      Real.log x ≤ 2 * Real.sqrt x := by
    have hx0 : 0 ≤ x := (by norm_num : (0 : ℝ) ≤ 1).trans hx
    calc
      Real.log x = 2 * Real.log (Real.sqrt x) := by
        rw [Real.log_sqrt hx0]
        ring
      _ ≤ 2 * (Real.sqrt x - 1) := by
        gcongr
        exact Real.log_le_sub_one_of_pos (by positivity)
      _ ≤ 2 * Real.sqrt x := by nlinarith
  let C : ℝ := 12800 / delta
  let R : ℝ := max 256 (max 4 (C ^ 2))
  let L : Nat := Nat.ceil R + 1
  have hR256 : (256 : ℝ) ≤ R := by dsimp [R]; exact le_max_left _ _
  have hR4 : (4 : ℝ) ≤ R := by
    dsimp [R]
    exact le_trans (by norm_num) (le_max_right _ _)
  have hRC : C ^ 2 ≤ R := by
    dsimp [R]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hL4 : 4 ≤ L := by
    have h4ceil : 4 ≤ Nat.ceil R := by
      have h := Nat.le_ceil R
      have : (4 : ℝ) ≤ (Nat.ceil R : ℝ) := hR4.trans h
      exact_mod_cast this
    dsimp [L]
    omega
  have hLpos : 0 < L := by omega
  refine ⟨L, hLpos, ?_⟩
  intro s k hs hsk
  have hspos : 0 < s := lt_of_lt_of_le (by omega) hs
  have hsR : (0 : ℝ) < s := by exact_mod_cast hspos
  let x : ℝ := (k : ℝ) / (s : ℝ)
  have hskR : (L : ℝ) * (s : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hsk
  have hxL : (L : ℝ) ≤ x := by
    dsimp [x]
    exact (le_div_iff₀ hsR).2 hskR
  have hx4 : (4 : ℝ) ≤ x := by
    have hL4R : (4 : ℝ) ≤ L := by exact_mod_cast hL4
    exact hL4R.trans hxL
  have hx256 : (256 : ℝ) ≤ x := by
    have hL256 : 256 ≤ L := by
      have h256ceil : 256 ≤ Nat.ceil R := by
        have h := Nat.le_ceil R
        have : (256 : ℝ) ≤ (Nat.ceil R : ℝ) := hR256.trans h
        exact_mod_cast this
      dsimp [L]
      omega
    have hL256R : (256 : ℝ) ≤ L := by exact_mod_cast hL256
    exact hL256R.trans hxL
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hlogx4 : (4 : ℝ) ≤ Real.log x := by
    have hlog256 : Real.log (256 : ℝ) = 8 * Real.log 2 := by
      rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
      norm_num
    have hlogmono : Real.log (256 : ℝ) ≤ Real.log x :=
      Real.log_le_log (by norm_num) hx256
    rw [hlog256] at hlogmono
    nlinarith
  have hxR : R ≤ x := by
    have hLR : (R : ℝ) ≤ L := by
      have h := Nat.le_ceil R
      dsimp [L]
      exact h.trans (by norm_num)
    exact hLR.trans hxL
  have hCx : C ^ 2 ≤ x := hRC.trans hxR
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hCsqrt : C ≤ Real.sqrt x := by
    apply (Real.le_sqrt hCpos.le (by positivity)).2
    exact hCx
  have hCdelta : 12800 ≤ delta * Real.sqrt x := by
    have hCsqrt' : 12800 / delta ≤ Real.sqrt x := by
      simpa [C] using hCsqrt
    have h := (div_le_iff₀ hdelta).mp hCsqrt'
    nlinarith
  have hsqrt_sq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (by positivity)
  have hprod : 12800 * Real.sqrt x ≤ delta * x := by
    have hmul := mul_le_mul_of_nonneg_right hCdelta (Real.sqrt_nonneg x)
    nlinarith [hsqrt_sq]
  have hB32 : 32 ≤ delta / 200 * x / Real.log x := by
    apply (le_div_iff₀ hlogpos).2
    have hmain : 64 * Real.sqrt x ≤ delta / 200 * x := by
      nlinarith [hprod]
    nlinarith [hlog_sqrt hx1]
  have hq_exists : ∃ q : Nat, (∃ m : Nat, q = 2 ^ m) ∧ 16 ≤ q ∧
      (q : ℝ) ≤ delta / 200 * x / Real.log x ∧
      delta / 200 * x / Real.log x ≤ 2 * q := by
    let B : ℝ := delta / 200 * x / Real.log x
    let N : Nat := Nat.floor B
    have hBpos : 0 < B := by dsimp [B]; positivity
    have hBnonneg : 0 ≤ B := hBpos.le
    have hN32 : 32 ≤ N := by
      apply Nat.le_floor
      simpa [B] using hB32
    let m : Nat := Nat.log 2 N
    let q : Nat := 2 ^ m
    have hNpos : N ≠ 0 := by omega
    have hqleN : q ≤ N := by
      dsimp [q, m]
      exact Nat.pow_log_le_self 2 hNpos
    have hm : 4 ≤ m := by
      dsimp [m]
      apply Nat.le_log_of_pow_le (by norm_num)
      norm_num
      omega
    have hq16' : 16 ≤ q := by
      dsimp [q]
      calc
        16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm
    have hqleB : (q : ℝ) ≤ B := by
      have hfloor : (N : ℝ) ≤ B := by
        simpa [N] using (Nat.floor_le hBnonneg)
      have hqleNreal : (q : ℝ) ≤ N := by exact_mod_cast hqleN
      exact hqleNreal.trans hfloor
    have hNlt : N < 2 * q := by
      dsimp [q, m]
      have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) N
      simpa [pow_succ, Nat.mul_comm] using h
    have hNsucc : N + 1 ≤ 2 * q := Nat.succ_le_of_lt hNlt
    have hBleq : B ≤ (2 * q : Nat) := by
      have hfloorlt := Nat.lt_floor_add_one B
      norm_num at hfloorlt ⊢
      exact le_trans hfloorlt.le (by exact_mod_cast hNsucc)
    exact ⟨q, ⟨m, rfl⟩, hq16', hqleB, by simpa [Nat.cast_mul] using hBleq⟩
  obtain ⟨q, hqpow2, hq16, hqle, hBle⟩ := hq_exists
  have hqprime : IsPrimePow q := by
    rcases hqpow2 with ⟨m, hm⟩
    subst q
    have hmpos : 0 < m := by
      by_contra hm0
      have hm' : m = 0 := Nat.eq_zero_of_not_pos hm0
      subst m
      norm_num at hq16
    exact (Nat.Prime.isPrimePow Nat.prime_two).pow hmpos.ne'
  refine ⟨q, hqpow2, hqprime, hq16, ?_, ?_, ?_⟩
  · simpa [x] using hqle
  · simpa [x] using hBle
  let K : Type := Fin q
  let hfintype : Fintype K := inferInstance
  have hqcard : IsPrimePow (Fintype.card K) := by
    simpa [K] using hqprime
  let hfield : Field K := Classical.choice ((Fintype.nonempty_field_iff).mpr hqcard)
  letI : Fintype K := hfintype
  letI : Field K := hfield
  have hKcard : @Fintype.card K hfintype = q := by
    simpa [K] using Fintype.card_fin q
  have ht : 2 ≤ s - 2 := by omega
  refine ⟨K, hfield, hfintype, hKcard, ht, ?_⟩
  · dsimp
    have hp := OldPolarityParameters K (s - 2) q ht hqprime hq16 hKcard
    dsimp at hp
    rcases hp with ⟨htri, n, d, lambda, hcard, hnform, hdform, hdeg,
      hlam, hspectral, hbilinear, hnlow, hnhigh, hdlow, hdhigh, hlamhigh,
      hpair⟩
    have htri' : ∀ (a b : Fin s → (PolarityGraph K (s - 2) ht).vertex),
        (∀ i, ¬ (PolarityGraph K (s - 2) ht).adj (a i) (b i)) →
        (∀ ⦃i j : Fin s⦄, i.val < j.val →
          (PolarityGraph K (s - 2) ht).adj (a i) (b j)) → False := by
      have heq : s - 2 + 2 = s := by omega
      intro a b hdiag hupper
      apply htri (fun i => a (Fin.cast heq i)) (fun i => b (Fin.cast heq i))
      · intro i
        exact hdiag (Fin.cast heq i)
      · intro i j hij
        apply hupper (i := Fin.cast heq i) (j := Fin.cast heq j)
        simpa [Fin.cast] using hij
    have hprops := OldPairDigraphProperties (PolarityGraph K (s - 2) ht) s htri'
    refine ⟨htri', hprops.2, hpair, ?_⟩
    let G : LoopGraph := PolarityGraph K (s - 2) ht
    letI : Fintype G.vertex := G.fintype
    letI : DecidableEq G.vertex := Classical.decEq _
    letI : DecidableRel G.adj := G.decidableAdj
    have hmix := ExpanderMixing G.adj n d lambda
      hcard hbilinear
    have hpack : Fintype.card (PolarityGraph K (s - 2) ht).vertex = n ∧
        n = (q ^ ((s - 2) + 1) - 1) / (q - 1) ∧
        d = (q ^ (s - 2) - 1) / (q - 1) ∧
        (∀ v : (PolarityGraph K (s - 2) ht).vertex,
          Fintype.card {u : (PolarityGraph K (s - 2) ht).vertex //
            (PolarityGraph K (s - 2) ht).adj v u} = d) ∧
        lambda = Real.sqrt ((d : ℝ) -
          ((((q ^ ((s - 2) - 1) - 1) / (q - 1) : Nat) : ℝ))) ∧
        NonprincipalSpectralBound (PolarityGraph K (s - 2) ht) lambda ∧
        (q : ℝ) ^ (s - 2) / 2 ≤ n ∧ (n : ℝ) ≤ 2 * (q : ℝ) ^ (s - 2) ∧
        (q : ℝ) ^ ((s - 2) - 1) / 2 ≤ d ∧
        (d : ℝ) ≤ 2 * (q : ℝ) ^ ((s - 2) - 1) ∧
        lambda ≤ 2 * Real.sqrt d := by
      exact ⟨hcard, hnform, hdform, hdeg, hlam, hspectral, hnlow,
        hnhigh, hdlow, hdhigh, hlamhigh⟩
    by_cases hsmall : delta ≤ 5
    · have hqposR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
      have hlogq_nonneg : 0 ≤ Real.log (q : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
      have hqle_x : (q : ℝ) ≤ x := by
        have hlog2x : Real.log 2 ≤ Real.log x :=
          Real.log_le_log (by norm_num) (by linarith [hx4])
        have hcoef : delta / 200 ≤ Real.log x := by
          nlinarith [hlogtwo, hlog2x]
        have hBlex : delta / 200 * x / Real.log x ≤ x := by
          apply (div_le_iff₀ hlogpos).2
          have hxpos : 0 < x := by linarith
          have hm := mul_le_mul_of_nonneg_right hcoef (le_of_lt hxpos)
          nlinarith [hm]
        exact hqle.trans hBlex
      have hlogqx : Real.log (q : ℝ) ≤ Real.log x :=
        Real.log_le_log hqposR hqle_x
      let Lq : Nat := Nat.ceil (Real.log (q : ℝ))
      have hLq : (Lq : ℝ) < Real.log x + 1 := by
        have h := Nat.ceil_lt_add_one hlogq_nonneg
        calc
          (Lq : ℝ) < Real.log (q : ℝ) + 1 := h
          _ ≤ Real.log x + 1 := by linarith
      have hLqx : (Lq : ℝ) ≤ (5 / 4 : ℝ) * Real.log x := by
        nlinarith [hLq, hlogx4]
      have hqLq : (q : ℝ) * Lq ≤
          (delta / 200 * x / Real.log x) * ((5 / 4 : ℝ) * Real.log x) := by
        calc
          (q : ℝ) * Lq ≤
              (delta / 200 * x / Real.log x) * Lq :=
            mul_le_mul_of_nonneg_right hqle (by positivity)
          _ ≤ (delta / 200 * x / Real.log x) *
              ((5 / 4 : ℝ) * Real.log x) :=
            mul_le_mul_of_nonneg_left hLqx (by positivity)
      have hs2R : (0 : ℝ) ≤ (s : ℝ) - 2 := by
        have hs4 : (4 : ℝ) ≤ s := by exact_mod_cast (show 4 ≤ s by omega)
        linarith
      have hs2cast : ((s - 2 : Nat) : ℝ) = (s : ℝ) - 2 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      have hWreal : (32 : ℝ) * (s - 2) * q * Lq ≤
          delta / 5 * k := by
        calc
          (32 : ℝ) * (s - 2) * q * Lq =
              (32 : ℝ) * (s - 2) * ((q : ℝ) * Lq) := by ring
          _ ≤ 32 * (s - 2) *
              ((delta / 200 * x / Real.log x) * ((5 / 4 : ℝ) * Real.log x)) := by
            exact mul_le_mul_of_nonneg_left hqLq (by positivity)
          _ = delta / 5 * (s - 2) * x := by
            field_simp
            ring
          _ ≤ delta / 5 * k := by
            have htx : (s - 2 : ℝ) * x ≤ k := by
              calc
                (s - 2 : ℝ) * x ≤ s * x := by
                  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
                _ = k := by
                  dsimp [x]
                  field_simp
            have hmul := mul_le_mul_of_nonneg_left htx
              (show (0 : ℝ) ≤ delta / 5 by positivity)
            nlinarith [hmul]
      have hWk : 32 * (s - 2) * q * Lq ≤ k := by
        have hreal :
            ((32 * (s - 2) * q * Lq : Nat) : ℝ) ≤ (k : ℝ) := by
          have hright : delta / 5 * (k : ℝ) ≤ (k : ℝ) := by
            have hkR : (0 : ℝ) ≤ k := by positivity
            nlinarith [hsmall]
          calc
            ((32 * (s - 2) * q * Lq : Nat) : ℝ) =
                32 * ((s - 2 : Nat) : ℝ) * (q : ℝ) * (Lq : ℝ) := by norm_num
            _ = 32 * ((s : ℝ) - 2) * (q : ℝ) * (Lq : ℝ) := by rw [hs2cast]
            _ ≤ delta / 5 * (k : ℝ) := hWreal
            _ ≤ (k : ℝ) := hright
        exact_mod_cast hreal
      have hnpos : 0 < n := by
        have hqpowpos : 0 < (q : ℝ) ^ (s - 2) := by positivity
        have hnposR : (0 : ℝ) < n := by nlinarith [hnlow]
        exact_mod_cast hnposR
      have hdpos : 0 < d := by
        have hqpowpos : 0 < (q : ℝ) ^ ((s - 2) - 1) := by positivity
        have hdposR : (0 : ℝ) < d := by nlinarith [hdlow]
        exact_mod_cast hdposR
      have hcoh := OldCoherentTreeCount K (s - 2) q k hqprime hq16 hKcard ht
        n d lambda hpack hmix hnpos hdpos hWk
      let W : Nat := 32 * (s - 2) * q * Lq
      have hWk' : W ≤ k := by simpa [W] using hWk
      have hcohW : (ForwardIndependentCount
          (OldPairDigraph (PolarityGraph K (s - 2) ht)) k : ℝ) ≤
          (8 : ℝ) ^ k * (lambda ^ 2 / d ^ 2) ^ (k - W) *
            (n : ℝ) ^ (2 * k) := by simpa [W] using hcoh
      have hq2 : 2 ≤ q := by omega
      have hqposN : 0 < q := by omega
      have hpow : q ^ ((s - 2) - 1) ≤ q ^ (s - 2) :=
        Nat.pow_le_pow_right hqposN (by omega)
      have haN : ((q ^ ((s - 2) - 1) - 1) / (q - 1)) ≤ d := by
        rw [hdform]
        exact Nat.div_le_div_right (Nat.sub_le_sub_right hpow 1)
      let a0 : Nat := (q ^ ((s - 2) - 1) - 1) / (q - 1)
      have hda : a0 ≤ d := by simpa [a0] using haN
      have hdaR : 0 ≤ (d : ℝ) - a0 := by
        have hda' : (a0 : ℝ) ≤ d := by exact_mod_cast hda
        linarith
      have hlam_sq : lambda ^ 2 = (d : ℝ) - a0 := by
        rw [hlam]
        simpa [a0] using (Real.sq_sqrt hdaR)
      have hlam_le_d : lambda ^ 2 ≤ (d : ℝ) := by
        have ha0R : (0 : ℝ) ≤ a0 := by positivity
        nlinarith [hlam_sq, ha0R]
      have hdqN : q ^ ((s - 2) - 1) ≤ d := by
        rw [hdform, ← Nat.geomSum_eq hq2]
        apply Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        exact Finset.mem_range.mpr (by omega)
      have hdposR : (0 : ℝ) < d := by exact_mod_cast hdpos
      have hdqR : (q : ℝ) ^ ((s - 2) - 1) ≤ d := by exact_mod_cast hdqN
      have hqpowR : 0 < (q : ℝ) ^ ((s - 2) - 1) := by positivity
      have hratio : lambda ^ 2 / (d : ℝ) ^ 2 ≤
          1 / (q : ℝ) ^ ((s - 2) - 1) := by
        calc
          lambda ^ 2 / (d : ℝ) ^ 2 ≤ (d : ℝ) / (d : ℝ) ^ 2 := by
            exact div_le_div_of_nonneg_right hlam_le_d (sq_nonneg _)
          _ = 1 / (d : ℝ) := by field_simp
          _ ≤ 1 / (q : ℝ) ^ ((s - 2) - 1) := by
            apply (div_le_div_iff₀ hdposR hqpowR).2
            nlinarith [hdqR]
      have hratio_pow : (lambda ^ 2 / (d : ℝ) ^ 2) ^ (k - W) ≤
          (1 / (q : ℝ) ^ ((s - 2) - 1)) ^ (k - W) :=
        pow_le_pow_left₀ (by positivity) hratio _
      have hnupper : (n : ℝ) ≤ 2 * (q : ℝ) ^ (s - 2) := hnhigh
      have hn_pow : (n : ℝ) ^ (2 * k) ≤
          (2 * (q : ℝ) ^ (s - 2)) ^ (2 * k) := by
        exact pow_le_pow_left₀ (by positivity) hnupper _
      have hrough : (ForwardIndependentCount
          (OldPairDigraph (PolarityGraph K (s - 2) ht)) k : ℝ) ≤
          (8 : ℝ) ^ k * (1 / (q : ℝ) ^ ((s - 2) - 1)) ^ (k - W) *
            (2 * (q : ℝ) ^ (s - 2)) ^ (2 * k) := by
        calc
          (ForwardIndependentCount
              (OldPairDigraph (PolarityGraph K (s - 2) ht)) k : ℝ) ≤
              (8 : ℝ) ^ k * (lambda ^ 2 / d ^ 2) ^ (k - W) *
                (n : ℝ) ^ (2 * k) := hcohW
          _ ≤ (8 : ℝ) ^ k *
              (1 / (q : ℝ) ^ ((s - 2) - 1)) ^ (k - W) *
                (n : ℝ) ^ (2 * k) := by
            gcongr
          _ ≤ _ := by
            gcongr
      let Aexp : Nat := ((s - 2) - 1) * (k - W)
      let Bexp : Nat := (s - 2) * (2 * k)
      let Eexp : Nat := Bexp - Aexp
      have hAleB : Aexp ≤ Bexp := by
        dsimp [Aexp, Bexp]
        calc
          ((s - 2) - 1) * (k - W) ≤ (s - 2) * k := by
            exact Nat.mul_le_mul (by omega) (Nat.sub_le _ _)
          _ ≤ (s - 2) * (2 * k) := by
            exact Nat.mul_le_mul_left _ (by omega)
      have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqposR
      have hpowdiv : (q : ℝ) ^ Eexp =
          (q : ℝ) ^ Bexp * ((q : ℝ) ^ Aexp)⁻¹ := by
        dsimp [Eexp]
        exact pow_sub₀ (q : ℝ) hqne hAleB
      have halgebra : (8 : ℝ) ^ k *
          (1 / (q : ℝ) ^ ((s - 2) - 1)) ^ (k - W) *
          (2 * (q : ℝ) ^ (s - 2)) ^ (2 * k) =
          32 ^ k * (q : ℝ) ^ Eexp := by
        rw [div_pow, one_pow, mul_pow]
        rw [one_div]
        rw [← pow_mul, ← pow_mul]
        dsimp [Aexp, Bexp] at hpowdiv ⊢
        have hconst : (8 : ℝ) ^ k * (2 : ℝ) ^ (2 * k) = 32 ^ k := by
          calc
            (8 : ℝ) ^ k * (2 : ℝ) ^ (2 * k) =
                8 ^ k * (2 ^ 2) ^ k := by rw [pow_mul]
            _ = (8 * 2 ^ 2) ^ k := by rw [← mul_pow]
            _ = 32 ^ k := by norm_num
        calc
          (8 : ℝ) ^ k * ((q : ℝ) ^ (((s - 2) - 1) * (k - W)))⁻¹ *
              ((2 : ℝ) ^ (2 * k) * (q : ℝ) ^ ((s - 2) * (2 * k))) =
              ((8 : ℝ) ^ k * (2 : ℝ) ^ (2 * k)) *
                (q : ℝ) ^ ((s - 2) * (2 * k)) *
                ((q : ℝ) ^ (((s - 2) - 1) * (k - W)))⁻¹ := by ring
          _ = (32 : ℝ) ^ k * (q : ℝ) ^ ((s - 2) * (2 * k)) *
                ((q : ℝ) ^ (((s - 2) - 1) * (k - W)))⁻¹ := by rw [hconst]
          _ = (32 : ℝ) ^ k *
                ((q : ℝ) ^ ((s - 2) * (2 * k)) *
                  ((q : ℝ) ^ (((s - 2) - 1) * (k - W)))⁻¹) := by ring
          _ = (32 : ℝ) ^ k * (q : ℝ) ^ Eexp := by
            exact congrArg (fun z : ℝ => (32 : ℝ) ^ k * z) hpowdiv.symm
      have hWdelta : (W : ℝ) ≤ delta / 5 * (k : ℝ) := by
        dsimp [W]
        calc
          ((32 * (s - 2) * q * Lq : Nat) : ℝ) =
              32 * ((s - 2 : Nat) : ℝ) * (q : ℝ) * (Lq : ℝ) := by norm_num
          _ = 32 * ((s : ℝ) - 2) * (q : ℝ) * (Lq : ℝ) := by rw [hs2cast]
          _ ≤ delta / 5 * (k : ℝ) := hWreal
      have hEcast : (Eexp : ℝ) =
          (s - 2 : ℝ) * (2 * k) - ((s - 2) - 1 : ℝ) * (k - W) := by
        have hBcast : (Bexp : ℝ) = (s - 2 : ℝ) * (2 * k) := by
          dsimp [Bexp]
          rw [Nat.cast_mul, Nat.cast_mul, hs2cast]
          norm_num
        have hAcast : (Aexp : ℝ) =
            ((s - 2 : ℝ) - 1) * ((k : ℝ) - W) := by
          dsimp [Aexp]
          rw [Nat.cast_mul, Nat.cast_sub hWk']
          rw [Nat.cast_sub (by omega), hs2cast]
          norm_num
        calc
          (Eexp : ℝ) = (Bexp : ℝ) - (Aexp : ℝ) := by
            dsimp [Eexp]
            exact Nat.cast_sub hAleB
          _ = (s - 2 : ℝ) * (2 * k) -
              ((s - 2 : ℝ) - 1) * ((k : ℝ) - W) := by
            rw [hBcast, hAcast]
      let Etar : ℝ := 2 * (s - 2) - (s - 3) * (1 - delta / 5)
      have hEtar_final : Etar =
          2 * ((s - 2 : Nat) : ℝ) - ((s - 3 : Nat) : ℝ) *
            (1 - delta / 5) := by
        dsimp [Etar]
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        ring
      have hmulW : ((s - 2) - 1 : ℝ) * (W : ℝ) ≤
          ((s - 2) - 1 : ℝ) * (delta / 5 * (k : ℝ)) := by
        have hs3 : (0 : ℝ) ≤ (s : ℝ) - 3 := by
          have hs4 : (4 : ℝ) ≤ s := by exact_mod_cast (show 4 ≤ s by omega)
          linarith
        exact mul_le_mul_of_nonneg_left hWdelta (by linarith)
      have hEle : (Eexp : ℝ) ≤ Etar * (k : ℝ) := by
        dsimp [Etar]
        nlinarith [hEcast, hmulW]
      have hqone : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
      have hqexpR : (q : ℝ) ^ (Eexp : ℝ) ≤
          (q : ℝ) ^ (Etar * (k : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hqone hEle
      have hqexp : (q : ℝ) ^ Eexp ≤
          (q : ℝ) ^ (Etar * (k : ℝ)) := by
        calc
          (q : ℝ) ^ Eexp = (q : ℝ) ^ (Eexp : ℝ) :=
            (Real.rpow_natCast (q : ℝ) Eexp).symm
          _ ≤ _ := hqexpR
      have htarget : (32 * Real.rpow (q : ℝ) Etar) ^ k =
          32 ^ k * (q : ℝ) ^ (Etar * (k : ℝ)) := by
        rw [mul_pow]
        congr 1
        calc
          (Real.rpow (q : ℝ) Etar) ^ k =
              (Real.rpow (q : ℝ) Etar) ^ (k : ℝ) :=
            (Real.rpow_natCast _ k).symm
          _ = Real.rpow (q : ℝ) (Etar * (k : ℝ)) := by
            exact (Real.rpow_mul (by positivity) Etar (k : ℝ)).symm
      calc
        (ForwardIndependentCount
            (OldPairDigraph (PolarityGraph K (s - 2) ht)) k : ℝ) ≤
            (8 : ℝ) ^ k * (1 / (q : ℝ) ^ ((s - 2) - 1)) ^ (k - W) *
              (2 * (q : ℝ) ^ (s - 2)) ^ (2 * k) := hrough
        _ = 32 ^ k * (q : ℝ) ^ Eexp := halgebra
        _ ≤ 32 ^ k * (q : ℝ) ^ (Etar * (k : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hqexp (by positivity)
        _ = (32 * Real.rpow (q : ℝ) Etar) ^ k := htarget.symm
        _ = (32 * Real.rpow (q : ℝ)
            (2 * ((s - 2 : Nat) : ℝ) - ((s - 3 : Nat) : ℝ) *
              (1 - delta / 5))) ^ k := by rw [hEtar_final]
    · have hlarge : 5 < delta := by linarith
      let D : LooplessDigraph := OldPairDigraph (PolarityGraph K (s - 2) ht)
      letI : Fintype D.vertex := D.fintype
      have hqone : (1 : ℝ) ≤ q := by
        exact_mod_cast (show 1 ≤ q by omega)
      have hambient : (ForwardIndependentCount D k : ℝ) ≤
          (Fintype.card D.vertex : ℝ) ^ k := by
        have h := Fintype.card_subtype_le
          (p := fun f : Fin k → D.vertex =>
            ∀ ⦃i j : Fin k⦄, i.val < j.val → ¬ D.arc (f i) (f j))
        have h' : ForwardIndependentCount D k ≤
            Fintype.card (Fin k → D.vertex) := by
          simpa [ForwardIndependentCount] using h
        have h'' : ForwardIndependentCount D k ≤
            Fintype.card D.vertex ^ k := by
          simpa [Fintype.card_fun] using h'
        exact_mod_cast h''
      have hDcardN : Fintype.card D.vertex ≤ n * n := by
        have hsub : Fintype.card D.vertex ≤
            Fintype.card (G.vertex × G.vertex) := by
          exact Fintype.card_subtype_le _
        have hGcard : Fintype.card G.vertex = n := by
          simpa [G] using hcard
        calc
          Fintype.card D.vertex ≤ Fintype.card (G.vertex × G.vertex) := hsub
          _ = n * n := by rw [Fintype.card_prod, hGcard]
      have hDcard : (Fintype.card D.vertex : ℝ) ≤ (n : ℝ) ^ 2 := by
        have h : (Fintype.card D.vertex : ℝ) ≤ (n * n : Nat) := by
          exact_mod_cast hDcardN
        simpa [pow_two] using h
      have hDupper : (Fintype.card D.vertex : ℝ) ≤
          4 * (q : ℝ) ^ (2 * (s - 2)) := by
        calc
          (Fintype.card D.vertex : ℝ) ≤ (n : ℝ) ^ 2 := hDcard
          _ ≤ (2 * (q : ℝ) ^ (s - 2)) ^ 2 := by
            gcongr
          _ = 4 * (q : ℝ) ^ (2 * (s - 2)) := by
            calc
              (2 * (q : ℝ) ^ (s - 2)) ^ 2 =
                  4 * ((q : ℝ) ^ (s - 2)) ^ 2 := by ring
              _ = 4 * (q : ℝ) ^ ((s - 2) * 2) := by rw [← pow_mul]
              _ = 4 * (q : ℝ) ^ (2 * (s - 2)) := by
                rw [Nat.mul_comm]
      let Etar : ℝ := 2 * (s - 2) - (s - 3) * (1 - delta / 5)
      have hEtar_final : Etar =
          2 * ((s - 2 : Nat) : ℝ) - ((s - 3 : Nat) : ℝ) *
            (1 - delta / 5) := by
        dsimp [Etar]
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        ring
      have hE : ((2 * (s - 2) : Nat) : ℝ) ≤ Etar := by
        dsimp [Etar]
        have hs3 : (0 : ℝ) ≤ (s : ℝ) - 3 := by
          have hs4 : (4 : ℝ) ≤ s := by exact_mod_cast (show 4 ≤ s by omega)
          linarith
        rw [Nat.cast_mul, Nat.cast_sub (by omega)]
        nlinarith [hlarge, hs3]
      have hqexpR : (q : ℝ) ^ ((2 * (s - 2) : Nat) : ℝ) ≤
          (q : ℝ) ^ Etar := by
        apply Real.rpow_le_rpow_of_exponent_le hqone hE
      have hqexp : (q : ℝ) ^ (2 * (s - 2)) ≤
          (q : ℝ) ^ Etar := by
        calc
          (q : ℝ) ^ (2 * (s - 2)) =
              (q : ℝ) ^ ((2 * (s - 2) : Nat) : ℝ) := by
            exact (Real.rpow_natCast (q : ℝ) (2 * (s - 2))).symm
          _ ≤ _ := hqexpR
      have hbase : 4 * (q : ℝ) ^ (2 * (s - 2)) ≤
          32 * Real.rpow (q : ℝ) Etar := by
        have hqpos : (0 : ℝ) < q := by positivity
        have hnonneg : 0 ≤ Real.rpow (q : ℝ) Etar :=
          Real.rpow_nonneg hqpos.le _
        calc
          4 * (q : ℝ) ^ (2 * (s - 2)) ≤
              4 * Real.rpow (q : ℝ) Etar :=
            mul_le_mul_of_nonneg_left hqexp (by norm_num)
          _ ≤ 32 * Real.rpow (q : ℝ) Etar := by
            exact mul_le_mul_of_nonneg_right (by norm_num) hnonneg
      have hpow : (4 * (q : ℝ) ^ (2 * (s - 2))) ^ k ≤
          (32 * Real.rpow (q : ℝ) Etar) ^ k := by
        exact pow_le_pow_left₀ (by positivity) hbase _
      have hDtarget : (Fintype.card D.vertex : ℝ) ^ k ≤
          (32 * Real.rpow (q : ℝ) Etar) ^ k := by
        exact (pow_le_pow_left₀ (by positivity) hDupper _).trans hpow
      calc
        (ForwardIndependentCount
            (OldPairDigraph (PolarityGraph K (s - 2) ht)) k : ℝ) =
            (ForwardIndependentCount D k : ℝ) := by rfl
        _ ≤ (Fintype.card D.vertex : ℝ) ^ k := hambient
        _ ≤ (32 * Real.rpow (q : ℝ) Etar) ^ k := hDtarget
        _ = (32 * Real.rpow (q : ℝ)
            (2 * ((s - 2 : Nat) : ℝ) - ((s - 3 : Nat) : ℝ) *
              (1 - delta / 5))) ^ k := by rw [hEtar_final]
