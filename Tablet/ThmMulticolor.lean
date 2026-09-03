import Tablet.F2ForwardIndependentBound
import Tablet.MulticolorRamseyNumber
import Tablet.RandomHomomorphismColoring
import Tablet.FiniteRamseyPositivity

open scoped BigOperators
set_option maxHeartbeats 5000000

-- [TABLET NODE: ThmMulticolor]
theorem ThmMulticolor :
    ∀ ell : Nat, 3 ≤ ell → ∃ c : ℝ, 0 < c ∧ ∃ S : Nat,
      ∀ s : Nat, S ≤ s →
        (MulticolorRamseyNumber s ell : ℝ) ≥
          c * Real.rpow 2 (((ell - 1 : Nat) : ℝ) * (s : ℝ) / 2) := by
-- BODY
  classical
  have hsum_bound : ∀ s : Nat, 4 ≤ s →
      (∑ t ∈ Finset.Icc 1 (s - 1),
        Nat.choose s t * 2 ^ ((s - 1) * (t + s) - Nat.choose (t + 1) 2)) ≤
      2 ^ ((3 * s * s + 4 - 5 * s) / 2 + s) := by
    intro s hs
    let B : Nat := (3 * s * s + 4 - 5 * s) / 2
    have hterm : ∀ t ∈ Finset.Icc 1 (s - 1),
        Nat.choose s t * 2 ^ ((s - 1) * (t + s) - Nat.choose (t + 1) 2) ≤
          Nat.choose s t * 2 ^ B := by
      intro t ht
      have ht' := Finset.mem_Icc.mp ht
      have hchoose : Nat.choose (t + 1) 2 = (t + 1) * t / 2 := by
        simpa [Nat.choose_two_right, Nat.mul_comm]
      rw [hchoose]
      let a : Nat := (s - 1) * (t + s)
      let p : Nat := (t + 1) * t
      let b : Nat := p / 2
      let u : Nat := s - 1 - t
      have hs2 : s = t + u + 1 := by dsimp [u]; omega
      have hdivlow : p ≤ 2 * b + 1 := by dsimp [b]; omega
      have hpoly : 2 * a + 1 + 5 * s ≤ 3 * s * s + 4 + p := by
        dsimp [a, p]
        rw [hs2]
        simp only [Nat.add_sub_cancel]
        have hident :
            3 * (t + u + 1) * (t + u + 1) + 4 + (t + 1) * t =
              2 * ((t + u) * (t + (t + u + 1))) + 1 + 5 * (t + u + 1) +
                u * (u - 1) + 1 := by
          cases u with
          | zero => ring
          | succ u => simp; ring
        rw [hident]
        omega
      have h2 : 2 * a + 5 * s ≤ 3 * s * s + 4 + 2 * b := by omega
      have hsub2 : 2 * a - 2 * b + 5 * s ≤ 3 * s * s + 4 := by
        have hR : 5 * s ≤ 3 * s * s + 4 := by nlinarith
        by_cases hab : 2 * b ≤ 2 * a
        · omega
        · have hz : 2 * a - 2 * b = 0 := by omega
          omega
      have hE : 2 * (a - b) + 5 * s ≤ 3 * s * s + 4 := by
        simpa [Nat.mul_sub_left_distrib] using hsub2
      have hE' : 2 * (a - b) ≤ 3 * s * s + 4 - 5 * s :=
        Nat.le_sub_of_add_le hE
      have hEB : a - b ≤ B := by
        dsimp [B]
        apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
        simpa [Nat.mul_comm] using hE'
      have hp : 2 ^ (a - b) ≤ 2 ^ B :=
        Nat.pow_le_pow_right (by omega) hEB
      exact Nat.mul_le_mul_left _ hp
    have hsumterm :
        (∑ t ∈ Finset.Icc 1 (s - 1),
          Nat.choose s t * 2 ^ ((s - 1) * (t + s) - Nat.choose (t + 1) 2)) ≤
          (∑ t ∈ Finset.Icc 1 (s - 1), Nat.choose s t) * 2 ^ B := by
      calc
        _ ≤ ∑ t ∈ Finset.Icc 1 (s - 1), Nat.choose s t * 2 ^ B := by
          apply Finset.sum_le_sum
          intro t ht
          exact hterm t ht
        _ = _ := by rw [Finset.sum_mul]
    have hsub : Finset.Icc 1 (s - 1) ⊆ Finset.range (s + 1) := by
      intro t ht
      simp only [Finset.mem_Icc, Finset.mem_range] at ht ⊢
      omega
    have hchoose_sum :
        (∑ t ∈ Finset.Icc 1 (s - 1), Nat.choose s t) ≤ 2 ^ s := by
      calc
        _ ≤ ∑ t ∈ Finset.range (s + 1), Nat.choose s t := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro t ht hnot
          positivity
        _ = 2 ^ s := by simpa using Nat.sum_range_choose s
    have hsum :
        (∑ t ∈ Finset.Icc 1 (s - 1),
          Nat.choose s t * 2 ^ ((s - 1) * (t + s) - Nat.choose (t + 1) 2)) ≤
        2 ^ s * 2 ^ B := hsumterm.trans (Nat.mul_le_mul_right _ hchoose_sum)
    calc
      _ ≤ 2 ^ s * 2 ^ B := hsum
      _ = 2 ^ (B + s) := by rw [← Nat.pow_add]; congr 1 <;> omega
      _ = _ := by rfl
  intro ell hell
  let L : Nat := ell - 1
  have hL : 0 < L := by dsimp [L]; omega
  have hL2 : 2 ≤ L := by dsimp [L]; omega
  let cconst : ℝ := Real.rpow 2 (-((9 : ℝ) / 2) * (L : ℝ))
  have hcconst : 0 < cconst := by
    dsimp [cconst]
    positivity
  refine ⟨cconst, hcconst, 16, ?_⟩
  intro s hs
  have hs4 : 4 ≤ s := by omega
  have hs16 : 16 ≤ s := by omega
  have hRmem0 : ∀ (m : Nat), 2 ≤ m → ∀ (G : LoopGraph),
      @Fintype.card G.vertex G.fintype = RamseyNumber s m →
      (∀ v, ¬ G.adj v v) →
      Nonempty (CliqueWitness G s) ∨ Nonempty (IndependentWitness G m) := by
    intro m hm2 G hcard hloop
    have hposR : 0 < RamseyNumber s m :=
      FiniteRamseyPositivity s m (by omega) hm2
    have hmem := Nat.sInf_mem (Nat.nonempty_of_pos_sInf hposR)
    simpa [RamseyNumber] using hmem G hcard hloop
  have hmulti : ∀ colors : Nat, 1 ≤ colors → ∃ m : Nat, 2 ≤ m ∧
      ∀ c : CompleteColoring m colors,
        Nonempty (MonochromaticClique c s) := by
    intro colors hcolors
    induction colors with
    | zero => omega
    | succ colors ih =>
        by_cases hzero : colors = 0
        · subst colors
          refine ⟨s, (by omega), ?_⟩
          intro c
          refine ⟨{ vertex := fun i => i
                    injective := by intro i j h; exact h
                    monochromatic := ?_ }⟩
          refine ⟨0, ?_⟩
          intro i j hij
          apply Fin.ext
          omega
        · have hpos : 1 ≤ colors := by omega
          obtain ⟨m, hm2, hm⟩ := ih hpos
          let R : Nat := RamseyNumber s m
          have hR2 : 2 ≤ R := by
            dsimp [R]
            by_contra hsmall
            have hone : RamseyNumber s m = 1 := by
              have hposR : 0 < RamseyNumber s m :=
                FiniteRamseyPositivity s m (by omega) hm2
              omega
            let G0 : LoopGraph :=
              { vertex := Fin 1
                fintype := inferInstance
                adj := fun _ _ => False
                decidableAdj := inferInstance
                symmetric := by intro u v; simp }
            have hres := hRmem0 m hm2 G0 (by simp [G0, hone]) (by
              intro v hv
              exact hv)
            rcases hres with ⟨⟨cl⟩⟩ | ⟨⟨ind⟩⟩
            · let i0 : Fin s := ⟨0, by omega⟩
              let i1 : Fin s := ⟨1, by omega⟩
              have h01 : i0 ≠ i1 := by
                intro h
                have hv := congrArg Fin.val h
                dsimp [i0, i1] at hv
                omega
              exact h01 (cl.injective (Subsingleton.elim _ _))
            · let i0 : Fin m := ⟨0, by omega⟩
              let i1 : Fin m := ⟨1, by omega⟩
              have h01 : i0 ≠ i1 := by
                intro h
                have hv := congrArg Fin.val h
                dsimp [i0, i1] at hv
                omega
              exact h01 (ind.injective (Subsingleton.elim _ _))
          refine ⟨R, hR2, ?_⟩
          intro c
          let G : LoopGraph :=
            { vertex := Fin R
              fintype := inferInstance
              adj := fun u v => c.color u v = 0 ∧ u ≠ v
              decidableAdj := inferInstance
              symmetric := by
                intro u v
                constructor
                · rintro ⟨huv, hne⟩
                  exact ⟨by simpa [c.symmetric] using huv, Ne.symm hne⟩
                · rintro ⟨hvu, hne⟩
                  exact ⟨by simpa [c.symmetric] using hvu, Ne.symm hne⟩ }
          have hres := hRmem0 m hm2 G (by simp [G, R]) (by
            intro v hv
            exact hv.2 rfl)
          rcases hres with ⟨⟨cl⟩⟩ | ⟨⟨ind⟩⟩
          · refine ⟨{ vertex := cl.vertex
                      injective := cl.injective
                      monochromatic := ?_ }⟩
            refine ⟨0, ?_⟩
            intro i j hij
            exact (cl.adjacent hij).1
          · let zero : Fin colors := ⟨0, by omega⟩
            let shift : Fin (colors + 1) → Fin colors := fun x =>
              if hx : x.val = 0 then zero else ⟨x.val - 1, by omega⟩
            let c' : CompleteColoring m colors :=
              { color := fun i j => shift (c.color (ind.vertex i) (ind.vertex j))
                symmetric := by intro i j; simp [c.symmetric] }
            obtain ⟨mc⟩ := hm c'
            refine ⟨{ vertex := fun i => ind.vertex (mc.vertex i)
                      injective := ?_
                      monochromatic := ?_ }⟩
            · intro i j hij
              apply mc.injective
              exact ind.injective hij
            · rcases mc.monochromatic with ⟨color, hcolor⟩
              refine ⟨⟨color.val + 1, by omega⟩, ?_⟩
              intro i j hij
              have hne : (c.color (ind.vertex (mc.vertex i))
                  (ind.vertex (mc.vertex j))).val ≠ 0 := by
                intro hz
                have hz' : c.color (ind.vertex (mc.vertex i))
                    (ind.vertex (mc.vertex j)) = 0 := by
                  apply Fin.ext
                  exact hz
                have hind := ind.independent (i := mc.vertex i) (j := mc.vertex j)
                  (by intro h; exact hij (mc.injective h))
                apply hind
                exact ⟨hz', by intro h; exact hij (mc.injective (ind.injective h))⟩
              have hh := hcolor hij
              dsimp [c', shift] at hh
              split at hh
              next hz => exact (hne hz).elim
              next hz =>
                apply Fin.ext
                have hval : (c.color (ind.vertex (mc.vertex i))
                    (ind.vertex (mc.vertex j))).val - 1 = color.val := by
                  have hv := congrArg Fin.val hh
                  simpa [hz] using hv
                have hzpos : 1 ≤ (c.color (ind.vertex (mc.vertex i))
                    (ind.vertex (mc.vertex j))).val :=
                  Nat.one_le_iff_ne_zero.mpr hne
                calc
                  (c.color (ind.vertex (mc.vertex i))
                      (ind.vertex (mc.vertex j))).val =
                      (c.color (ind.vertex (mc.vertex i))
                        (ind.vertex (mc.vertex j))).val - 1 + 1 :=
                    (Nat.sub_add_cancel hzpos).symm
                  _ = color.val + 1 := by rw [hval]
  obtain ⟨M, hM2, hM⟩ := hmulti ell (by omega)
  let Good : Set Nat := {n : Nat | ∀ c : CompleteColoring n ell,
    Nonempty (MonochromaticClique c s)}
  have hGood : Good.Nonempty := ⟨M, by simpa [Good] using hM⟩
  have hRmem : ∀ c : CompleteColoring (MulticolorRamseyNumber s ell) ell,
      Nonempty (MonochromaticClique c s) := by
    have hmem := Nat.sInf_mem hGood
    simpa [MulticolorRamseyNumber, Good] using hmem
  let A : Nat := s / 2 - 4
  let B : Nat := (3 * s * s + 4 - 5 * s) / 2
  let n : Nat := 2 ^ (A * L)
  obtain ⟨D, hD, hfree, hN, hF⟩ := F2ForwardIndependentBound s s hs4 le_rfl
  have hNlow : 2 ^ (2 * s - 4) ≤ @Fintype.card D.vertex D.fintype := by
    rw [hN]
    have hexp : 2 * s - 3 = (2 * s - 4) + 1 := by omega
    have he : s - 2 ≤ 2 * s - 4 := by omega
    have hy : 2 ^ (s - 2) ≤ 2 ^ (2 * s - 4) :=
      Nat.pow_le_pow_right (by omega) he
    rw [hexp, Nat.pow_succ]
    omega
  have hsum := hsum_bound s hs4
  have hFnat : ForwardIndependentCount D s ≤ 2 ^ (B + s) := by
    have hsum' :
        (∑ t ∈ Finset.Icc 1 (s - 1),
          Nat.choose s t * 2 ^ ((s - 1) * (t + s) - Nat.choose (t + 1) 2)) ≤
        2 ^ (B + s) := by simpa [B] using hsum
    have hFsum : ForwardIndependentCount D s ≤
        (∑ t ∈ Finset.Icc 1 (s - 1),
          Nat.choose s t * 2 ^ ((s - 1) * (t + s) - Nat.choose (t + 1) 2)) := by
      exact_mod_cast hF
    exact hFsum.trans (by simpa [B] using hsum)
  have hnat : Nat.choose n s * (ForwardIndependentCount D s) ^ L <
      (@Fintype.card D.vertex D.fintype) ^ (s * L) := by
    have hA : 2 * A + 8 ≤ s := by dsimp [A]; omega
    have hAmul : 2 * A * s + 8 * s ≤ s * s := by
      have h := Nat.mul_le_mul_right s hA
      simpa [Nat.add_mul] using h
    have hB : 2 * B + 5 * s ≤ 3 * s * s + 4 := by
      have h0 : 2 * B ≤ 3 * s * s + 4 - 5 * s := by
        dsimp [B]
        exact Nat.mul_div_le _ _
      have hR : 5 * s ≤ 3 * s * s + 4 := by nlinarith
      omega
    have hgap : A * s + B + s < (2 * s - 4) * s := by
      have hgap0 : A * s + B + s + 4 * s < 2 * s * s := by nlinarith
      have hsub : A * s + B + s < 2 * s * s - 4 * s := Nat.lt_sub_of_add_lt hgap0
      have hAprod : A * s = s / 2 * s - 4 * s := by
        dsimp [A]
        rw [Nat.mul_sub_right_distrib]
      simpa only [Nat.mul_sub_right_distrib, hAprod] using hsub
    have hgapL := Nat.mul_lt_mul_of_pos_right hgap hL
    have hexp : A * L * s + (B + s) * L < (2 * s - 4) * (s * L) := by
      calc
        _ = (A * s + B + s) * L := by ring
        _ < ((2 * s - 4) * s) * L := hgapL
        _ = _ := by ring
    have hpowlt : 2 ^ (A * L * s + (B + s) * L) <
        2 ^ ((2 * s - 4) * (s * L)) := Nat.pow_lt_pow_right (by omega) hexp
    have hchoose : Nat.choose n s ≤ n ^ s := Nat.choose_le_pow _ _
    have hFpow : (ForwardIndependentCount D s) ^ L ≤ (2 ^ (B + s)) ^ L :=
      Nat.pow_le_pow_left hFnat L
    have hupper : Nat.choose n s * (ForwardIndependentCount D s) ^ L ≤
        2 ^ (A * L * s + (B + s) * L) := by
      calc
        _ ≤ n ^ s * (2 ^ (B + s)) ^ L := Nat.mul_le_mul hchoose hFpow
        _ = 2 ^ (A * L * s + (B + s) * L) := by
          dsimp [n]
          rw [← pow_mul, ← pow_mul, ← pow_add]
    have hNpow : (2 ^ (2 * s - 4)) ^ (s * L) ≤
        (@Fintype.card D.vertex D.fintype) ^ (s * L) :=
      Nat.pow_le_pow_left hNlow _
    have hNpow' : 2 ^ ((2 * s - 4) * (s * L)) ≤
        (@Fintype.card D.vertex D.fintype) ^ (s * L) := by
      calc
        _ = (2 ^ (2 * s - 4)) ^ (s * L) := by rw [pow_mul]
        _ ≤ _ := hNpow
    exact hupper.trans_lt (hpowlt.trans_le hNpow')
  have hprob : (Nat.choose n s : ℝ) *
      ((ForwardIndependentCount D s : ℝ) /
        (@Fintype.card D.vertex D.fintype : ℝ) ^ s) ^ L < 1 := by
    have hstrictR : (Nat.choose n s : ℝ) *
        (ForwardIndependentCount D s : ℝ) ^ L <
        (@Fintype.card D.vertex D.fintype : ℝ) ^ (s * L) := by
      exact_mod_cast hnat
    have hNpos : 0 < @Fintype.card D.vertex D.fintype := by
      have : 0 < 2 ^ (2 * s - 4) := by positivity
      omega
    rw [div_pow]
    have hpow : ((@Fintype.card D.vertex D.fintype : ℝ) ^ s) ^ L =
        (@Fintype.card D.vertex D.fintype : ℝ) ^ (s * L) := by rw [← pow_mul]
    rw [hpow, ← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity :
      (0 : ℝ) < (@Fintype.card D.vertex D.fintype : ℝ) ^ (s * L))).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hstrictR
  have hDpos : 0 < @Fintype.card D.vertex D.fintype := by
    exact lt_of_lt_of_le (by positivity) hNlow
  obtain ⟨col, hcol⟩ := RandomHomomorphismColoring D s ell n (by omega)
      (by omega) hDpos hfree hprob
  have hRlower : n < MulticolorRamseyNumber s ell := by
    by_contra hnot
    have hle : MulticolorRamseyNumber s ell ≤ n := Nat.le_of_not_gt hnot
    let c := col
    have hc := hcol
    let ι : Fin (MulticolorRamseyNumber s ell) → Fin n :=
      fun i => Fin.castLE hle i
    let c0 : CompleteColoring (MulticolorRamseyNumber s ell) ell :=
      { color := fun i j => c.color (ι i) (ι j)
        symmetric := by intro i j; simp [c.symmetric] }
    obtain ⟨mc⟩ := hRmem c0
    apply hc
    refine ⟨{ vertex := fun i => ι (mc.vertex i)
              injective := ?_
              monochromatic := ?_ }⟩
    · intro i j hij
      apply mc.injective
      apply Fin.ext
      simpa [ι] using congrArg Fin.val hij
    · rcases mc.monochromatic with ⟨color, hcolor⟩
      exact ⟨color, by intro i j hij; exact hcolor hij⟩
  have hfloorNat : s ≤ 2 * A + 9 := by dsimp [A]; omega
  have hfloor : (s : ℝ) / 2 - (9 : ℝ) / 2 ≤ (A : ℝ) := by
    have hh : (s : ℝ) ≤ 2 * (A : ℝ) + 9 := by exact_mod_cast hfloorNat
    linarith
  have hmul := mul_le_mul_of_nonneg_right hfloor (by positivity : (0 : ℝ) ≤ (L : ℝ))
  have hexponent :
      (L : ℝ) * (s : ℝ) / 2 - ((9 : ℝ) / 2) * (L : ℝ) ≤
        ((A * L : Nat) : ℝ) := by
    rw [Nat.cast_mul]
    nlinarith
  have hnreal : (n : ℝ) = Real.rpow 2 ((A * L : Nat) : ℝ) := by
    dsimp [n]
    rw [Nat.cast_pow]
    exact (Real.rpow_natCast (2 : ℝ) (A * L)).symm
  have hpowreal : Real.rpow 2
      ((L : ℝ) * (s : ℝ) / 2 - ((9 : ℝ) / 2) * (L : ℝ)) ≤ (n : ℝ) := by
    rw [hnreal]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
  have htarget : cconst * Real.rpow 2 ((L : ℝ) * (s : ℝ) / 2) ≤ (n : ℝ) := by
    calc
      cconst * Real.rpow 2 ((L : ℝ) * (s : ℝ) / 2) =
          Real.rpow 2 (((L : ℝ) * (s : ℝ) / 2 - ((9 : ℝ) / 2) * (L : ℝ))) := by
            dsimp [cconst]
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
            congr 1
            ring
      _ ≤ (n : ℝ) := hpowreal
  have hRreal : (n : ℝ) < (MulticolorRamseyNumber s ell : ℝ) := by
    exact_mod_cast hRlower
  exact le_trans htarget hRreal.le
