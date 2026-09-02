import Tablet.ForwardIndependentCount
import Tablet.AlonRodlBound
import Tablet.RootedTreeCounting
import Tablet.TransitiveTournament
import Tablet.PolarityGraph
import Tablet.OldPolarityParameters
import Tablet.ExpanderMixing
import Tablet.ForwardIndependentTuple
import Tablet.DStarMarkedTreeBound
import Mathlib.FieldTheory.Cardinality

set_option maxHeartbeats 2000000

-- [TABLET NODE: DStarCounting]
theorem DStarCounting (t : Nat) (ht : 2 ≤ t) :
    ∃ C : Nat, 0 < C ∧
      ∀ q : Nat, C ≤ q → (∃ m : Nat, q = 2 ^ m) →
        ∀ k : Nat, C * q * (Nat.log q) ^ 2 ≤ k →
          ∃ D : LooplessDigraph,
            ¬ Nonempty (TransitiveTournament D (t + 1)) ∧
            (q ^ (2 * t - 1) / 4 : Nat) ≤
              @Fintype.card D.vertex D.fintype ∧
            (ForwardIndependentCount D k : ℝ) ≤
              (C * q ^ t : ℝ) ^ k := by
-- BODY
  classical
  let A : Nat := 20000 * t * t * (t + 1)
  let C : Nat := max 64 (max (2 * t * A) (4 * A))
  have hC : 0 < C := by
    dsimp [C]
    omega
  refine ⟨C, hC, ?_⟩
  intro q hq hqpow k hk
  obtain ⟨m, hqm⟩ := hqpow
  have hqpos : 0 < q := by omega
  have hq16 : 16 ≤ q := by omega
  have hqone : 1 < q := by omega
  have hlog : Nat.log 2 q = m := by
    rw [hqm]
    exact Nat.log_pow (by norm_num) m
  have hk2 : C * q * (Nat.log 2 q) ^ 2 ≤ k := by
    have hkfun := hk (q ^ m)
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.ofNat_apply, Pi.natCast_apply] at hkfun
    rw [Nat.log_pow hqone m] at hkfun
    have hkfun' : C * q * m ^ 2 ≤ k := by exact_mod_cast hkfun
    simpa [hlog] using hkfun'
  have hqprime : IsPrimePow q := by
    subst q
    have hmpos : 0 < m := by
      by_contra hm0
      have hm' : m = 0 := Nat.eq_zero_of_not_pos hm0
      subst m
      norm_num at hq16
    exact (Nat.Prime.isPrimePow Nat.prime_two).pow hmpos.ne'
  let K : Type := Fin q
  let hfintype : Fintype K := inferInstance
  have hKcard : @Fintype.card K hfintype = q := by
    simpa [K] using Fintype.card_fin q
  have hqcard : IsPrimePow (Fintype.card K) := by
    simpa [K] using hqprime
  let hfield : Field K := Classical.choice ((Fintype.nonempty_field_iff).mpr hqcard)
  letI : Fintype K := hfintype
  letI : Field K := hfield
  letI : Mul K := hfield.toMul
  letI : Add K := hfield.toAdd
  have hp := OldPolarityParameters K t q ht hqprime hq16 hKcard
  dsimp at hp
  rcases hp with ⟨htri, n, d, lambda, hcard, hnform, hdform, hdeg,
    hlam, hspectral, hbilinear, hnlow, hnhigh, hdlow, hdhigh, hlamhigh,
    hpair⟩
  let G : LoopGraph := PolarityGraph K t ht
  letI : Fintype G.vertex := G.fintype
  letI : DecidableEq G.vertex := Classical.decEq _
  letI : DecidableRel G.adj := G.decidableAdj
  let D : LooplessDigraph := {
    vertex := {p : G.vertex × G.vertex // G.adj p.1 p.2}
    fintype := inferInstance
    arc := fun u v => G.adj u.1.1 v.1.2 ∧ ¬ G.adj v.1.1 u.1.2
    decidableArc := inferInstance
    loopless := by
      intro u hu
      exact hu.2 hu.1
  }
  have hDcard : @Fintype.card D.vertex D.fintype = n * d := by
    let e : D.vertex ≃ Σ a : G.vertex, {b : G.vertex // G.adj a b} := {
      toFun := fun x => ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
      invFun := fun x => ⟨(x.1, x.2.1), x.2.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
    }
    rw [Fintype.card_congr e, Fintype.card_sigma]
    have hdeg' : ∀ v : G.vertex, Fintype.card {u : G.vertex // G.adj v u} = d := by
      simpa [G] using hdeg
    simp_rw [hdeg']
    have hcard' : Fintype.card G.vertex = n := by simpa [G] using hcard
    simp [hcard']
  have hDlower : (q ^ (2 * t - 1) / 4 : Nat) ≤
      @Fintype.card D.vertex D.fintype := by
    rw [hDcard]
    have hnlowN : q ^ t ≤ 2 * n := by
      have h : (q ^ t : ℝ) ≤ 2 * n := by nlinarith [hnlow]
      exact_mod_cast h
    have hdlowN : q ^ (t - 1) ≤ 2 * d := by
      have h : (q ^ (t - 1) : ℝ) ≤ 2 * d := by nlinarith [hdlow]
      exact_mod_cast h
    apply (Nat.div_le_iff_le_mul_add_pred (by omega : 0 < 4)).2
    have hbound : q ^ (2 * t - 1) ≤ n * d * 4 := by
      calc
        q ^ (2 * t - 1) = q ^ t * q ^ (t - 1) := by
          rw [show 2 * t - 1 = t + (t - 1) by omega, pow_add]
        _ ≤ (2 * n) * (2 * d) := Nat.mul_le_mul hnlowN hdlowN
        _ = n * d * 4 := by ring
    exact hbound.trans (by omega)
  have hDfrees : ¬ Nonempty (TransitiveTournament D (t + 1)) := by
    rintro ⟨tt⟩
    let a : Fin (t + 1) → G.vertex := fun i => (tt.vertex i).1.1
    let b : Fin (t + 1) → G.vertex := fun i => (tt.vertex i).1.2
    have hdiag : ∀ i, G.adj (a i) (b i) := by
      intro i
      exact (tt.vertex i).2
    have hforw : ∀ ⦃i j : Fin (t + 1)⦄, i.val < j.val →
        G.adj (a i) (b j) := by
      intro i j hij
      have h := tt.forwardArc hij
      change G.adj (a i) (b j) ∧ ¬ G.adj (a j) (b i) at h
      exact h.1
    have hback : ∀ ⦃i j : Fin (t + 1)⦄, i.val < j.val →
        ¬ G.adj (a j) (b i) := by
      intro i j hij
      have h := tt.forwardArc hij
      change G.adj (a i) (b j) ∧ ¬ G.adj (a j) (b i) at h
      exact h.2
    let xa : Fin (t + 1) → (Fin (t + 1) → K) := fun i => (a i).rep
    let yb : Fin (t + 1) → (Fin (t + 1) → K) := fun i => (b i).rep
    have hxa : ∀ i, xa i ≠ 0 := by
      intro i
      exact Projectivization.rep_nonzero _
    have hyb : ∀ i, yb i ≠ 0 := by
      intro i
      exact Projectivization.rep_nonzero _
    have hdotdiag : ∀ i, xa i ⬝ᵥ yb i = 0 := by
      intro i
      apply (Projectivization.orthogonal_mk (hxa i) (hyb i)).mp
      have ha : Projectivization.mk K (xa i) (hxa i) = a i := by
        simpa [xa] using (a i).mk_rep
      have hb : Projectivization.mk K (yb i) (hyb i) = b i := by
        simpa [yb] using (b i).mk_rep
      rw [ha, hb]
      simpa [G, PolarityGraph] using hdiag i
    have hdotforw : ∀ ⦃i j : Fin (t + 1)⦄, i.val < j.val →
        xa i ⬝ᵥ yb j = 0 := by
      intro i j hij
      apply (Projectivization.orthogonal_mk (hxa i) (hyb j)).mp
      have ha : Projectivization.mk K (xa i) (hxa i) = a i := by
        simpa [xa] using (a i).mk_rep
      have hb : Projectivization.mk K (yb j) (hyb j) = b j := by
        simpa [yb] using (b j).mk_rep
      rw [ha, hb]
      simpa [G, PolarityGraph] using hforw hij
    have hdotback : ∀ ⦃i j : Fin (t + 1)⦄, i.val < j.val →
        xa j ⬝ᵥ yb i ≠ 0 := by
      intro i j hij hz
      apply hback hij
      change Projectivization.orthogonal (a j) (b i)
      have ha : Projectivization.mk K (xa j) (hxa j) = a j := by
        simpa [xa] using (a j).mk_rep
      have hb : Projectivization.mk K (yb i) (hyb i) = b i := by
        simpa [yb] using (b i).mk_rep
      rw [← ha, ← hb]
      apply (Projectivization.orthogonal_mk (hxa j) (hyb i)).mpr
      simpa [xa, yb] using hz
    have hlin : LinearIndependent K yb := by
      rw [Fintype.linearIndependent_iff]
      intro c hrel i
      by_contra hci
      let S : Finset (Fin (t + 1)) := Finset.univ.filter (fun j => c j ≠ 0)
      have hS : S.Nonempty := by
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hci⟩⟩
      let i0 : Fin (t + 1) := S.min' hS
      have hi0S : i0 ∈ S := Finset.min'_mem S hS
      have hi0nz : c i0 ≠ 0 := (Finset.mem_filter.mp hi0S).2
      have hprior : ∀ l : Fin (t + 1), l.val < i0.val → c l = 0 := by
        intro l hli
        by_contra hcl
        have hlS : l ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcl⟩
        have hle := Finset.min'_le S l hlS
        omega
      by_cases hlast : i0.val = t
      · have hsum : (∑ l, c l • yb l) = c i0 • yb i0 := by
          apply Finset.sum_eq_single i0
          · intro l hl hli
            have hlt : l.val < i0.val := by omega
            simp [hprior l hlt]
          · simp
        have hzero : c i0 • yb i0 = 0 := by simpa [hrel] using hsum.symm
        rcases Function.ne_iff.mp (hyb i0) with ⟨u, hu⟩
        have hzero' := congrFun hzero u
        have hprod : c i0 * yb i0 u = 0 := by simpa using hzero'
        exact hi0nz ((mul_eq_zero.mp hprod).resolve_right hu)
      · let j : Fin (t + 1) := ⟨i0.val + 1, by omega⟩
        have hdot' : ∑ l, c l * (xa j ⬝ᵥ yb l) = 0 := by
          calc
            (∑ l, c l * (xa j ⬝ᵥ yb l)) =
                ∑ l, xa j ⬝ᵥ (c l • yb l) := by
                  apply Finset.sum_congr rfl
                  intro l hl
                  rw [dotProduct_smul]
                  rfl
            _ = xa j ⬝ᵥ (∑ l, c l • yb l) :=
                  (dotProduct_sum (xa j) (Finset.univ) (fun l => c l • yb l)).symm
            _ = 0 := by rw [hrel]; simp
        have hsum : ∑ l, c l * (xa j ⬝ᵥ yb l) =
            c i0 * (xa j ⬝ᵥ yb i0) := by
          rw [Finset.sum_eq_single i0]
          intro l hl hli
          rcases lt_or_gt_of_ne hli with hlt | hgt
          · rw [hprior l hlt, zero_mul]
          · by_cases hlj : l = j
            · subst l
              rw [hdotdiag, mul_zero]
            · have hlj' : l.val ≠ i0.val + 1 := by
                intro he
                apply hlj
                apply Fin.ext
                exact he
              have hadj := hdotforw (i := j) (j := l) (by dsimp [j]; omega)
              rw [hadj, mul_zero]
          simp
        have hback' : xa j ⬝ᵥ yb i0 ≠ 0 := hdotback (i := i0) (j := j) (by
          dsimp [j]
          omega)
        have hprod : c i0 * (xa j ⬝ᵥ yb i0) = 0 := by rw [← hsum, hdot']
        exact hi0nz ((mul_eq_zero.mp hprod).resolve_right hback')
    have hspan : Submodule.span K (Set.range yb) = ⊤ := by
      apply hlin.span_eq_top_of_card_eq_finrank
      simp [Module.finrank_fin_fun]
    have horth : ∀ v : (Fin (t + 1) → K), xa 0 ⬝ᵥ v = 0 := by
      intro v
      have hv : v ∈ Submodule.span K (Set.range yb) := by
        rw [hspan]
        exact Submodule.mem_top
      induction hv using Submodule.span_induction with
      | mem v hv =>
          rcases hv with ⟨i, rfl⟩
          by_cases hi : i = 0
          · subst i
            exact hdotdiag 0
          · have hi0 : i.val ≠ 0 := by
              intro hz
              apply hi
              apply Fin.ext
              exact hz
            have hlt : (0 : Nat) < i.val := by omega
            exact hdotforw hlt
      | zero => simp
      | add x y hx hy ihx ihy =>
          rw [dotProduct_add]
          rw [ihx, ihy]
          simp
      | smul c x hx ih =>
          change (xa 0) ⬝ᵥ (c • x) = 0
          rw [dotProduct_smul, ih]
          simp
    have : xa 0 = 0 := (dotProduct_eq_zero_iff.mp horth)
    exact hxa 0 this
  have hcount : (ForwardIndependentCount D k : ℝ) ≤ (C * q ^ t : ℝ) ^ k := by
    have hAmark : 20000 * t * t * (t + 1) ≤ A := by
      dsimp [A]
      exact le_rfl
    have hCA : 2 * t * A ≤ C := by
      dsimp [C]
      exact le_trans (by gcongr <;> norm_num)
        (le_trans (le_max_left _ _) (le_max_right _ _))
    have hC4 : 4 * A ≤ C := by
      dsimp [C]
      exact le_trans (le_max_right _ _)
        (le_max_right _ _)
    have hmark := DStarMarkedTreeBound K t q k A C ht hq16 ⟨m, hqm⟩ hKcard
      n d lambda
      ⟨hcard, hdeg, hbilinear, hnlow, hnhigh, hdlow, hdhigh, hlamhigh⟩
      hAmark hCA hC4 hq hk2
    dsimp at hmark
    rcases hmark with ⟨count, hpath, hcount', hsupport⟩
    have htree := RootedTreeCounting k (A * q * Nat.log 2 q)
      (4 * q ^ (2 * t - 1)) (A * q ^ t) count hcount' hsupport
      (by
        have hAq : A ≤ q := by
          have hAC : A ≤ C := by
            dsimp [C]
            omega
          exact hAC.trans hq
        have hpow : q ^ (t + 1) ≤ q ^ (2 * t - 1) := by
          apply Nat.pow_le_pow_right
          · omega
          · omega
        calc
          A * q ^ t ≤ q * q ^ t := Nat.mul_le_mul_right _ hAq
          _ = q ^ (t + 1) := by rw [pow_succ]; ring
          _ ≤ q ^ (2 * t - 1) := hpow
          _ ≤ 4 * q ^ (2 * t - 1) := by omega)
      (by
        have hlogpos : 0 < Nat.log 2 q := by
          exact Nat.log_pos (by norm_num) (by omega)
        calc
          A * q * Nat.log 2 q ≤ A * q * (Nat.log 2 q) ^ 2 := by
            gcongr
            nlinarith
          _ ≤ k := by
            have hAC : A ≤ C := by
              dsimp [C]
              omega
            have hmul : A * q * (Nat.log 2 q) ^ 2 ≤
                C * q * (Nat.log 2 q) ^ 2 := by
              gcongr
            exact hmul.trans hk2)
    have hnat : ForwardIndependentCount D k ≤
        2 ^ k * (4 * q ^ (2 * t - 1)) ^ (A * q * Nat.log 2 q) *
          (A * q ^ t) ^ (k - A * q * Nat.log 2 q) := by
      rw [hpath]
      exact htree
    have hApos : 0 < A := by
      dsimp [A]
      positivity
    have hBpos : 0 < A * q ^ t := by positivity
    have hWk : A * q * Nat.log 2 q ≤ k := by
      have hlogpos : 0 < Nat.log 2 q := by
        exact Nat.log_pos (by norm_num) (by omega)
      calc
        A * q * Nat.log 2 q ≤ A * q * (Nat.log 2 q) ^ 2 := by
          gcongr
          nlinarith
        _ ≤ k := by
          have hAC : A ≤ C := by
            dsimp [C]
            omega
          have hmul : A * q * (Nat.log 2 q) ^ 2 ≤
              C * q * (Nat.log 2 q) ^ 2 := by
            gcongr
          exact hmul.trans hk2
    have hDelta : 4 * q ^ (2 * t - 1) ≤ q ^ (2 * t) := by
      have hq4 : 4 ≤ q := by omega
      rw [show 2 * t = (2 * t - 1) + 1 by omega, pow_succ]
      calc
        4 * q ^ (2 * t - 1) ≤ q * q ^ (2 * t - 1) :=
          Nat.mul_le_mul_right _ hq4
        _ = q ^ (2 * t - 1) * q := by ring
    have hcoef : 2 * t * A ≤ C := hCA
    have hexp : Nat.log 2 q * (2 * t * (A * q * Nat.log 2 q)) ≤ k := by
      calc
        Nat.log 2 q * (2 * t * (A * q * Nat.log 2 q)) =
            (2 * t * A) * (q * (Nat.log 2 q) ^ 2) := by ring
        _ ≤ C * (q * (Nat.log 2 q) ^ 2) := by
          exact Nat.mul_le_mul_right _ hcoef
        _ ≤ k := by simpa [Nat.mul_assoc] using hk2
    have hqtw : q ^ (2 * t * (A * q * Nat.log 2 q)) ≤ 2 ^ k := by
      let E : Nat := 2 * t * (A * q * Nat.log 2 q)
      have hE : m * E ≤ k := by
        simpa [E, hlog] using hexp
      calc
        q ^ E = (2 ^ m) ^ E := by rw [hqm]
        _ = 2 ^ (m * E) := by rw [← pow_mul]
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hE
    have hnat' : ForwardIndependentCount D k ≤
        2 ^ k * q ^ (2 * t * (A * q * Nat.log 2 q)) *
          (A * q ^ t) ^ k := by
      calc
        ForwardIndependentCount D k ≤
            2 ^ k * (4 * q ^ (2 * t - 1)) ^ (A * q * Nat.log 2 q) *
              (A * q ^ t) ^ (k - A * q * Nat.log 2 q) := hnat
        _ ≤ 2 ^ k * (q ^ (2 * t)) ^ (A * q * Nat.log 2 q) *
              (A * q ^ t) ^ k := by
          have hpowDelta :
              (4 * q ^ (2 * t - 1)) ^ (A * q * Nat.log 2 q) ≤
                (q ^ (2 * t)) ^ (A * q * Nat.log 2 q) :=
            Nat.pow_le_pow_left hDelta _
          have hpowH : (A * q ^ t) ^ (k - A * q * Nat.log 2 q) ≤
              (A * q ^ t) ^ k :=
            Nat.pow_le_pow_right hBpos (Nat.sub_le _ _)
          calc
            2 ^ k * (4 * q ^ (2 * t - 1)) ^ (A * q * Nat.log 2 q) *
                (A * q ^ t) ^ (k - A * q * Nat.log 2 q) ≤
              (2 ^ k * (q ^ (2 * t)) ^ (A * q * Nat.log 2 q)) *
                (A * q ^ t) ^ (k - A * q * Nat.log 2 q) :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hpowDelta)
            _ ≤ (2 ^ k * (q ^ (2 * t)) ^ (A * q * Nat.log 2 q)) *
                (A * q ^ t) ^ k :=
              Nat.mul_le_mul_left _ hpowH
        _ = 2 ^ k * q ^ (2 * t * (A * q * Nat.log 2 q)) *
              (A * q ^ t) ^ k := by
          rw [← pow_mul]
    have hreal : ForwardIndependentCount D k ≤
        2 ^ k * q ^ (2 * t * (A * q * Nat.log 2 q)) *
          (A * q ^ t) ^ k := hnat'
    have hfinalNat : ForwardIndependentCount D k ≤
        (C * q ^ t) ^ k := by
      calc
        ForwardIndependentCount D k ≤
            2 ^ k * q ^ (2 * t * (A * q * Nat.log 2 q)) *
              (A * q ^ t) ^ k := hreal
        _ ≤ 2 ^ k * 2 ^ k * (A * q ^ t) ^ k := by
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hqtw)
        _ = (4 * A * q ^ t) ^ k := by
          rw [← mul_pow, ← mul_pow]
          ring
        _ ≤ (C * q ^ t) ^ k := by
          apply Nat.pow_le_pow_left
          exact Nat.mul_le_mul_right _ hC4
    exact_mod_cast hfinalNat
  exact ⟨D, hDfrees, hDlower, hcount⟩
