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
        ∀ k : Nat, C * q * (Nat.log 2 q) ^ 2 ≤ k →
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
  have hk2 : C * q * (Nat.log 2 q) ^ 2 ≤ k := hk
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
  have hDupper : @Fintype.card D.vertex D.fintype ≤
      4 * q ^ (2 * t - 1) := by
    rw [hDcard]
    have hnupperN : n ≤ 2 * q ^ t := by
      exact_mod_cast hnhigh
    have hdupperN : d ≤ 2 * q ^ (t - 1) := by
      exact_mod_cast hdhigh
    calc
      n * d ≤ (2 * q ^ t) * (2 * q ^ (t - 1)) :=
        Nat.mul_le_mul hnupperN hdupperN
      _ = 4 * q ^ (2 * t - 1) := by
        rw [show 2 * t - 1 = t + (t - 1) by omega, pow_add]
        ring
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
    rcases hmark with ⟨mark, hroot, hchildren, hpathMark⟩
    letI : Fintype D.vertex := D.fintype
    letI : ∀ m : Nat, Fintype (ForwardIndependentTuple D m) := fun m =>
      Fintype.ofInjective (fun σ : ForwardIndependentTuple D m => σ.vertex) (by
        intro σ τ he
        cases σ
        cases τ
        simp_all)
    let Child : ∀ m : Nat, ForwardIndependentTuple D m → Type := fun m σ =>
      {v : D.vertex // ∀ i : Fin m, ¬ D.arc (σ.vertex i) v}
    let childTuple : ∀ (m : Nat) (σ : ForwardIndependentTuple D m),
        Child m σ → ForwardIndependentTuple D (m + 1) := fun m σ c =>
      { vertex := fun j => if hj : j.val < m then σ.vertex ⟨j.val, hj⟩ else c.1
        independent := by
          intro i j hij
          by_cases hj : j.val < m
          · by_cases hi : i.val < m
            · simpa [hj, hi] using σ.independent (by omega)
            · exfalso
              omega
          · have hjm : j.val = m := by omega
            by_cases hi : i.val < m
            · have hci := c.2 ⟨i.val, hi⟩
              simpa [hj, hi, hjm] using hci
            · omega }
    have child_prefix : ∀ (m : Nat) (σ : ForwardIndependentTuple D m)
        (c : Child m σ) (i : Fin m),
        (childTuple m σ c).vertex i.castSucc = σ.vertex i := by
      intro m σ c i
      simp [childTuple, i.isLt]
    let MarkedChild : ∀ (m : Nat) (σ : ForwardIndependentTuple D m), Type :=
      fun m σ => {c : Child m σ // mark (m + 1) (childTuple m σ c) = true}
    let RawMarked : ∀ (m : Nat) (σ : ForwardIndependentTuple D m), Type :=
      fun m σ => {τ : ForwardIndependentTuple D (m + 1) //
        (∀ i : Fin m, τ.vertex i.castSucc = σ.vertex i) ∧
          mark (m + 1) τ = true}
    have hraw : ∀ (m : Nat) (σ : ForwardIndependentTuple D m),
        Nat.card (RawMarked m σ) ≤ A * q ^ t := by
      intro m σ
      simpa [RawMarked] using hchildren m σ
    have hmarkedType : ∀ (m : Nat) (σ : ForwardIndependentTuple D m),
        Fintype (MarkedChild m σ) := by
      intro m σ
      dsimp [MarkedChild]
      infer_instance
    have hmarkedBound : ∀ (m : Nat) (σ : ForwardIndependentTuple D m),
        Fintype.card (MarkedChild m σ) ≤ A * q ^ t := by
      intro m σ
      let toRaw : MarkedChild m σ → RawMarked m σ := fun c =>
        ⟨childTuple m σ c.1, ⟨child_prefix m σ c.1, c.2⟩⟩
      have htoRaw : Function.Injective toRaw := by
        intro a b hab
        have hv := congrArg (fun τ : ForwardIndependentTuple D (m + 1) =>
            τ.vertex ⟨m, by omega⟩) (congrArg Subtype.val hab)
        apply Subtype.ext
        apply Subtype.ext
        simpa [toRaw, childTuple] using hv
      have hle := Fintype.card_le_of_injective toRaw htoRaw
      have hraw' := hraw m σ
      rw [Nat.card_eq_fintype_card] at hraw'
      exact hle.trans hraw'
    have hDcard' : Fintype.card D.vertex ≤ 4 * q ^ (2 * t - 1) := by
      simpa using hDupper
    have hallBound : ∀ (m : Nat) (σ : ForwardIndependentTuple D m),
        Fintype.card (Child m σ) ≤ 4 * q ^ (2 * t - 1) := by
      intro m σ
      exact (Fintype.card_le_of_injective (fun c : Child m σ => c.1)
        (by intro a b h; exact Subtype.ext h)).trans hDcard'
    let p : (Fin k → D.vertex) → Prop := fun f =>
      ∀ ⦃i j : Fin k⦄, i.val < j.val → ¬ D.arc (f i) (f j)
    letI : DecidablePred p := fun f => Classical.propDecidable _
    letI : Fintype {f : Fin k → D.vertex // p f} :=
      Fintype.subtype (Finset.univ.filter p) (by
        intro f
        simp [p])
    let tupleOf : ∀ (r : Nat) (f : {f : Fin k → D.vertex // p f}),
        r ≤ k → ForwardIndependentTuple D r := fun r f hr =>
      { vertex := fun i => f.1 ⟨i.val, by omega⟩
        independent := by
          intro i j hij
          exact f.2 (by omega) }
    let takePrefix : ∀ {m : Nat} (σ : ForwardIndependentTuple D m)
        (r : Nat), r ≤ m → ForwardIndependentTuple D r :=
      fun {m} σ r hr =>
        { vertex := fun i => σ.vertex ⟨i.val, by omega⟩
          independent := by
            intro i j hij
            exact σ.independent (by omega) }
    let childOf : ∀ (f : {f : Fin k → D.vertex // p f}) (i : Fin k),
        Child i.val (tupleOf i.val f (by omega)) := fun f i =>
      ⟨f.1 i, by
        intro j
        have h := f.2 (i := ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩)
          (j := i) j.isLt
        simpa [tupleOf] using h⟩
    let sig : {f : Fin k → D.vertex // p f} → (Fin k → Bool) := fun f i =>
      if mark (i.val + 1)
          (childTuple i.val (tupleOf i.val f (by omega)) (childOf f i)) = true
      then false else true
    let Fiber (z : Fin k → Bool) :=
      {f : {f : Fin k → D.vertex // p f} // sig f = z}
    have hfiber : ∀ z : Fin k → Bool, Fintype (Fiber z) := by
      intro z
      dsimp [Fiber]
      infer_instance
    let g : ∀ (z : Fin k → Bool), Fiber z →
        (∀ i : Fin k, Fin (if z i = true then
          4 * q ^ (2 * t - 1) else A * q ^ t)) := fun z f i =>
      dite (z i = true)
        (fun hi =>
          let c : Child i.val (tupleOf i.val f.1 (by omega)) := childOf f.1 i
          let e := Fintype.equivFin (Child i.val
            (tupleOf i.val f.1 (by omega)))
          Fin.castLE (by
            simpa [hi] using hallBound i.val (tupleOf i.val f.1 (by omega))) (e c))
        (fun hi =>
          let c : MarkedChild i.val (tupleOf i.val f.1 (by omega)) :=
            ⟨childOf f.1 i, by
              have hs : sig f.1 i = false := by
                rw [congrFun f.2 i]
                exact Bool.eq_false_of_not_eq_true hi
              have hm : mark (i.val + 1)
                  (childTuple i.val (tupleOf i.val f.1 (by omega)) (childOf f.1 i)) = true := by
                cases hmval : mark (i.val + 1)
                    (childTuple i.val (tupleOf i.val f.1 (by omega)) (childOf f.1 i)) with
                | false => simp [sig, hmval] at hs
                | true => simpa using hmval
              exact hm⟩
          let e := Fintype.equivFin (MarkedChild i.val
            (tupleOf i.val f.1 (by omega)))
          Fin.castLE (by
            simpa [hi] using hmarkedBound i.val (tupleOf i.val f.1 (by omega))) (e c))
    have tuple_ext : ∀ (r : Nat) (a b : ForwardIndependentTuple D r),
        (∀ i, a.vertex i = b.vertex i) → a = b := by
      intro r a b hv
      cases a with
      | mk av ai =>
        cases b with
        | mk bv bi =>
          congr
          funext i
          exact hv i
    have htake : ∀ (f : {f : Fin k → D.vertex // p f}) (i : Fin k),
        takePrefix (tupleOf k f (by omega)) (i.val + 1) (by omega) =
          childTuple i.val (tupleOf i.val f (by omega)) (childOf f i) := by
      intro f i
      apply tuple_ext
      intro j
      by_cases hj : j.val < i.val
      · simp [takePrefix, tupleOf, childTuple, hj]
      · have hj' : j.val = i.val := by omega
        have hj'' : j = ⟨i.val, by omega⟩ := Fin.ext hj'
        rw [hj'']
        simp [takePrefix, tupleOf, childTuple, childOf]
    have hpath : ∀ (m : Nat) (σ : ForwardIndependentTuple D m),
        (∑ i : Fin m,
          if mark (i.val + 1)
              (takePrefix σ (i.val + 1) (by omega)) = false
          then 1 else 0) ≤ A * q * Nat.log 2 q := by
      intro m σ
      simpa [takePrefix] using hpathMark m σ
    have marked_rank_injective : ∀ (m : Nat)
        (σ1 σ2 : ForwardIndependentTuple D m)
        (c1 : MarkedChild m σ1) (c2 : MarkedChild m σ2), σ1 = σ2 →
        (Fintype.equivFin (MarkedChild m σ1) c1).val =
          (Fintype.equivFin (MarkedChild m σ2) c2).val →
        c1.1.1 = c2.1.1 := by
      intro m σ1 σ2 c1 c2 hσ hr
      subst σ2
      have hc : c1 = c2 := by
        apply (Fintype.equivFin _).injective
        apply Fin.ext
        exact hr
      exact congrArg (fun c => c.1.1) hc
    have child_rank_injective : ∀ (m : Nat)
        (σ1 σ2 : ForwardIndependentTuple D m)
        (c1 : Child m σ1) (c2 : Child m σ2), σ1 = σ2 →
        (Fintype.equivFin (Child m σ1) c1).val =
          (Fintype.equivFin (Child m σ2) c2).val →
        c1.1 = c2.1 := by
      intro m σ1 σ2 c1 c2 hσ hr
      subst σ2
      have hc : c1 = c2 := by
        apply (Fintype.equivFin _).injective
        apply Fin.ext
        exact hr
      exact congrArg (fun c => c.1) hc
    have hg : ∀ (z : Fin k → Bool), Function.Injective (g z) := by
      intro z f1 f2 heq
      apply Subtype.ext
      apply Subtype.ext
      funext i
      have hNat : ∀ n : Nat, ∀ j : Fin k, j.val = n → f1.1.1 j = f2.1.1 j := by
        intro n
        induction n using Nat.strong_induction_on with
        | h n ih =>
          intro j hj
          have prev : ∀ l : Fin j.val,
              f1.1.1 ⟨l.val, by omega⟩ = f2.1.1 ⟨l.val, by omega⟩ := by
            intro l
            let l' : Fin k := ⟨l.val, by omega⟩
            have llt : l.val < n := by omega
            exact ih l.val llt l' rfl
          have hσ : tupleOf j.val f1.1 (by omega) =
              tupleOf j.val f2.1 (by omega) := by
            apply tuple_ext
            exact prev
          have heqj := congrFun heq j
          by_cases hz : z j = true
          · let c1 : Child j.val (tupleOf j.val f1.1 (by omega)) := childOf f1.1 j
            let c2 : Child j.val (tupleOf j.val f2.1 (by omega)) := childOf f2.1 j
            simp only [g, dif_pos hz] at heqj
            have hr := congrArg Fin.val heqj
            apply child_rank_injective j.val
              (tupleOf j.val f1.1 (by omega))
              (tupleOf j.val f2.1 (by omega)) c1 c2 hσ
            simpa [c1, c2] using hr
          · simp only [g, dif_neg hz] at heqj
            have hs1 : sig f1.1 j = false := (congrFun f1.2 j).trans
              (Bool.eq_false_of_not_eq_true hz)
            have hs2 : sig f2.1 j = false := (congrFun f2.2 j).trans
              (Bool.eq_false_of_not_eq_true hz)
            let c1 : MarkedChild j.val (tupleOf j.val f1.1 (by omega)) :=
              ⟨childOf f1.1 j, by
                have hm : mark (j.val + 1)
                    (childTuple j.val (tupleOf j.val f1.1 (by omega)) (childOf f1.1 j)) = true := by
                  cases hmval : mark (j.val + 1)
                      (childTuple j.val (tupleOf j.val f1.1 (by omega)) (childOf f1.1 j)) with
                  | false => simp [sig, hmval] at hs1
                  | true => simpa using hmval
                exact hm⟩
            let c2 : MarkedChild j.val (tupleOf j.val f2.1 (by omega)) :=
              ⟨childOf f2.1 j, by
                have hm : mark (j.val + 1)
                    (childTuple j.val (tupleOf j.val f2.1 (by omega)) (childOf f2.1 j)) = true := by
                  cases hmval : mark (j.val + 1)
                      (childTuple j.val (tupleOf j.val f2.1 (by omega)) (childOf f2.1 j)) with
                  | false => simp [sig, hmval] at hs2
                  | true => simpa using hmval
                exact hm⟩
            have hr := congrArg Fin.val heqj
            apply marked_rank_injective j.val
              (tupleOf j.val f1.1 (by omega))
              (tupleOf j.val f2.1 (by omega)) c1 c2 hσ
            simpa [c1, c2] using hr
      exact hNat i.val i rfl
    have hcount' : ∀ z : Fin k → Bool, Fintype.card (Fiber z) ≤
        (4 * q ^ (2 * t - 1)) ^ (∑ i, if z i = true then 1 else 0) *
          (A * q ^ t) ^ (k - ∑ i, if z i = true then 1 else 0) := by
      intro z
      have hc := Fintype.card_le_of_injective (g z) (hg z)
      rw [Fintype.card_pi] at hc
      have hfilter :
          (Finset.univ.filter (fun i : Fin k => z i = false)).card =
            k - (Finset.univ.filter (fun i : Fin k => z i = true)).card := by
        have hsum := Finset.card_filter_add_card_filter_not
          (s := Finset.univ) (fun i : Fin k => z i = true)
        simp at hsum
        omega
      simpa [Finset.prod_ite, hfilter] using hc
    have hfi : ForwardIndependentCount D k =
        Fintype.card {f : Fin k → D.vertex // p f} := by
      simp [ForwardIndependentCount, p]
    let count : (Fin k → Bool) → Nat := fun z => Fintype.card (Fiber z)
    have hsum : (∑ z, count z) =
        Fintype.card {f : Fin k → D.vertex // p f} := by
      let e : (Σ z : Fin k → Bool, Fiber z) ≃
          {f : Fin k → D.vertex // p f} := Equiv.sigmaFiberEquiv sig
      rw [← Fintype.card_sigma]
      exact Fintype.card_congr e
    have hsupport : ∀ z, count z > 0 →
        (∑ i, if z i = true then 1 else 0) ≤ A * q * Nat.log 2 q := by
      intro z hz
      rcases Fintype.card_pos_iff.mp hz with ⟨f⟩
      have hp := hpath k (tupleOf k f.1 (by omega))
      have hsum_eq :
          (∑ i : Fin k, if z i = true then 1 else 0) =
            ∑ i : Fin k, if mark (i.val + 1)
                (takePrefix (tupleOf k f.1 (by omega)) (i.val + 1) (by omega)) = false
              then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hsig := congrFun f.2 i
        have hbool : mark (i.val + 1)
                (takePrefix (tupleOf k f.1 (by omega)) (i.val + 1) (by omega)) = false ↔
            z i = true := by
          rw [← hsig]
          rw [htake f.1 i]
          simp [sig]
        by_cases hzi : z i = true <;> by_cases hmi : mark (i.val + 1)
            (takePrefix (tupleOf k f.1 (by omega)) (i.val + 1) (by omega)) = false <;>
          simp_all
      rw [hsum_eq]
      exact hp
    have hpathCount : ForwardIndependentCount D k = ∑ z, count z :=
      hfi.trans hsum.symm
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
      rw [hpathCount]
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
