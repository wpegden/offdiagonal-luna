import Tablet.F2PairDigraph
import Tablet.OldPairDigraphProperties
import Tablet.TransitiveTournament

-- [TABLET NODE: F2PairDigraphProperties]
theorem F2PairDigraphProperties (s : Nat) (hs : 4 ≤ s) :
    (∀ v, ¬ (F2PairDigraph s).arc v v) ∧
      ¬ Nonempty (TransitiveTournament (F2PairDigraph s) s) ∧
      @Fintype.card (F2PairDigraph s).vertex (F2PairDigraph s).fintype =
        2 ^ (2 * s - 3) - 2 ^ (s - 2) := by
-- BODY
  classical
  let G : LoopGraph := {
    vertex := Fin (s - 1) → ZMod 2
    fintype := inferInstance
    adj := fun x y => ∑ i, x i * y i = 0
    decidableAdj := inferInstance
    symmetric := by
      intro x y
      simp [mul_comm]
  }
  have htri : ∀ (a b : Fin s → G.vertex),
      (∀ i, ¬ G.adj (a i) (b i)) →
      (∀ ⦃i j : Fin s⦄, i.val < j.val → G.adj (a i) (b j)) → False := by
    intro a b hdiag hfor
    change (∀ i, (∑ r, a i r * b i r) ≠ 0) at hdiag
    change (∀ ⦃i j : Fin s⦄, i.val < j.val →
      (∑ r, a i r * b j r) = 0) at hfor
    let lin : (Fin s → ZMod 2) → (Fin (s - 1) → ZMod 2) := fun c r =>
      ∑ i, c i * a i r
    have hlin_not_inj : ¬ Function.Injective lin := by
      intro hlin
      have hcard := Fintype.card_le_of_injective lin hlin
      simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin] at hcard
      have hpow : 2 ^ (s - 1) < 2 ^ s := by
        apply Nat.pow_lt_pow_right (by decide)
        omega
      omega
    obtain ⟨c, d, hlin_cd, hcd⟩ : ∃ c d, lin c = lin d ∧ c ≠ d := by
      rw [Function.not_injective_iff] at hlin_not_inj
      exact hlin_not_inj
    let e : Fin s → ZMod 2 := fun i => c i - d i
    have he : e ≠ 0 := by
      intro he0
      apply hcd
      funext i
      have hi := congrFun he0 i
      dsimp [e] at hi
      exact sub_eq_zero.mp hi
    have hrel : ∀ r, ∑ i, e i * a i r = 0 := by
      intro r
      have hr := congrFun hlin_cd r
      dsimp [lin, e] at hr ⊢
      calc
        ∑ i, (c i - d i) * a i r =
            ∑ i, (c i * a i r - d i * a i r) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [sub_mul]
        _ = (∑ i, c i * a i r) - ∑ i, d i * a i r := by
              rw [Finset.sum_sub_distrib]
        _ = 0 := sub_eq_zero.mpr hr
    obtain ⟨i, hi⟩ := Function.ne_iff.mp he
    let S : Finset (Fin s) := Finset.univ.filter (fun i => e i ≠ 0)
    have hS : S.Nonempty := by
      apply Finset.filter_nonempty_iff.mpr
      exact ⟨i, Finset.mem_univ _, hi⟩
    let j : Fin s := S.max' hS
    have hj : e j ≠ 0 := by
      exact (Finset.mem_filter.mp (Finset.max'_mem S hS)).2
    have hjmax : ∀ i, e i ≠ 0 → i.val ≤ j.val := by
      intro i hi
      exact Finset.le_max' S i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
    have hpair : ∑ i, e i * (∑ r, a i r * b j r) = 0 := by
      calc
        ∑ i, e i * (∑ r, a i r * b j r) =
            ∑ i, ∑ r, e i * (a i r * b j r) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.mul_sum]
        _ = ∑ r, ∑ i, e i * (a i r * b j r) := by
              rw [Finset.sum_comm]
        _ = ∑ r, (∑ i, e i * a i r) * b j r := by
              apply Finset.sum_congr rfl
              intro r hr
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = 0 := by simp [hrel]
    have hpair' : e j * (∑ r, a j r * b j r) = 0 := by
      calc
        e j * (∑ r, a j r * b j r) =
            ∑ i, e i * (∑ r, a i r * b j r) := by
          symm
          apply Finset.sum_eq_single j
          · intro i hi hne
            have hne' : i.val ≠ j.val := by
              intro heq
              exact hne (Fin.ext heq)
            have hlt_or : i.val < j.val ∨ j.val < i.val := lt_or_gt_of_ne hne'
            rcases hlt_or with hlt | hgt
            · rw [hfor hlt]
              simp
            · have hiz : e i = 0 := by
                by_contra hiz
                exact (not_lt_of_ge (hjmax i hiz)) hgt
              rw [hiz, zero_mul]
          · intro hjnot
            exact False.elim (hjnot (Finset.mem_univ j))
        _ = 0 := hpair
    have hdiagj : (∑ r, a j r * b j r) = 1 := by
      have hne := hdiag j
      have hcases : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by
        intro z
        fin_cases z
        · exact Or.inl rfl
        · exact Or.inr rfl
      rcases hcases (∑ r, a j r * b j r) with hzero | hone
      · exact False.elim (hne hzero)
      · exact hone
    rw [hdiagj, mul_one] at hpair'
    exact hj hpair'
  have hprops := OldPairDigraphProperties G s htri
  have hstruct :
      (∀ v, ¬ (F2PairDigraph s).arc v v) ∧
        ¬ Nonempty (TransitiveTournament (F2PairDigraph s) s) := by
    simpa [F2PairDigraph, G] using hprops
  have hcard : @Fintype.card (F2PairDigraph s).vertex (F2PairDigraph s).fintype =
      2 ^ (2 * s - 3) - 2 ^ (s - 2) := by
    let D : LooplessDigraph := F2PairDigraph s
    letI : Fintype D.vertex := D.fintype
    change @Fintype.card D.vertex D.fintype = _
    let X := Fin (s - 1) → ZMod 2
    let f : X → X → ZMod 2 := fun x y => ∑ i, x i * y i
    let P : X → X → Prop := fun x y => f x y ≠ 0
    letI (x : X) : DecidablePred (P x) := fun y => inferInstanceAs (Decidable (P x y))
    letI (x : X) : Fintype {y : X // P x y} := Fintype.ofFinite _
    have hdecomp : @Fintype.card D.vertex D.fintype =
        ∑ x, Fintype.card {y : X // P x y} := by
      let e : D.vertex ≃ Σ x, {y : X // P x y} :=
        { toFun := fun z => ⟨z.1.1, ⟨z.1.2, by
              simpa [D, F2PairDigraph, OldPairDigraph, P, X] using z.2⟩⟩
          invFun := fun z => ⟨(z.1, z.2.1), by
              simpa [D, F2PairDigraph, OldPairDigraph, P, X] using z.2.2⟩
          left_inv := by intro z; rfl
          right_inv := by intro z; rfl }
      rw [Fintype.card_congr e, Fintype.card_sigma]
    have hbinary : ∀ u : ZMod 2, u ≠ 0 → u = 1 := by
      intro u hu
      fin_cases u
      · exact (hu rfl).elim
      · rfl
    have hfiber : ∀ x : X,
        Fintype.card {y : X // P x y} =
          if x = 0 then 0 else 2 ^ (s - 2) := by
      intro x
      by_cases hx : x = 0
      · subst x
        letI : IsEmpty {y : X // P 0 y} := ⟨fun y => by
          apply y.2
          change (∑ i : Fin (s - 1), (0 : ZMod 2) * y.1 i) = 0
          simp⟩
        simp
      · obtain ⟨r, hr⟩ := Function.ne_iff.mp hx
        have hxr : x r = 1 := hbinary _ hr
        let z : X := Pi.single r 1
        have hz : f x z = 1 := by
          dsimp [f, z]
          have hsumz :
              (∑ i : Fin (s - 1), x i * (Pi.single r (1 : ZMod 2) : X) i) =
                x r * (Pi.single r (1 : ZMod 2) : X) r := by
            apply Finset.sum_eq_single r
            · intro i hi hne
              rw [Pi.single_eq_of_ne hne]
              simp
            · intro hr'
              exact False.elim (hr' (Finset.mem_univ r))
          rw [hsumz]
          simp [hxr]
        have hadd : ∀ y : X, f x (y + z) = f x y + f x z := by
          intro y
          dsimp [f]
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          change x i * (y i + z i) = x i * y i + x i * z i
          exact mul_add _ _ _
        have hchar : ∀ u : ZMod 2, u + u = 0 := by
          intro u
          fin_cases u <;> rfl
        have hzz : z + z = 0 := by
          funext i
          change z i + z i = 0
          exact hchar (z i)
        letI : Fintype {y : X // f x y = 0} := Fintype.ofFinite _
        letI : Fintype {y : X // f x y ≠ 0} := Fintype.ofFinite _
        let e : {y : X // f x y ≠ 0} ≃ {y : X // f x y = 0} :=
          { toFun := fun y => ⟨y.1 + z, by
                rw [hadd, hbinary _ y.2, hz]
                exact hchar 1⟩
            invFun := fun y => ⟨y.1 + z, by
                rw [hadd, y.2, hz]
                intro h
                have : (1 : ZMod 2) = 0 := by simpa using h
                exact one_ne_zero this⟩
            left_inv := by
              intro y
              apply Subtype.ext
              funext i
              have hi : z i + z i = 0 := by
                have hzi := congrFun hzz i
                change z i + z i = 0 at hzi
                exact hzi
              calc
                (y.1 i + z i) + z i = y.1 i + (z i + z i) := by ac_rfl
                _ = y.1 i := by rw [hi, add_zero]
            right_inv := by
              intro y
              apply Subtype.ext
              funext i
              have hi : z i + z i = 0 := by
                have hzi := congrFun hzz i
                change z i + z i = 0 at hzi
                exact hzi
              calc
                (y.1 i + z i) + z i = y.1 i + (z i + z i) := by ac_rfl
                _ = y.1 i := by rw [hi, add_zero] }
        have heq : Fintype.card {y : X // f x y ≠ 0} =
            Fintype.card {y : X // f x y = 0} := Fintype.card_congr e
        have hcompl := Fintype.card_subtype_compl (fun y : X => f x y = 0)
        have hcomp : Fintype.card {y : X // f x y ≠ 0} =
            Fintype.card X - Fintype.card {y : X // f x y = 0} := by
          simpa using hcompl
        have htotal : Fintype.card X =
            Fintype.card {y : X // f x y ≠ 0} +
              Fintype.card {y : X // f x y = 0} := by
          omega
        have hcardX : Fintype.card X = 2 ^ (s - 1) := by
          simp [X, Fintype.card_fun, ZMod.card]
        have hhalf : Fintype.card {y : X // f x y ≠ 0} = 2 ^ (s - 2) := by
          rw [heq] at htotal
          rw [hcardX] at htotal
          have hs' : s - 1 = (s - 2) + 1 := by omega
          rw [hs', Nat.pow_succ] at htotal
          omega
        simpa [P, hx] using hhalf
    have hsum : (∑ x : X, if x = 0 then 0 else 2 ^ (s - 2)) =
        (Fintype.card X - 1) * 2 ^ (s - 2) := by
      let S : Finset X := Finset.univ.filter (fun x => x ≠ 0)
      have hS : S.card = Fintype.card X - 1 := by
        rw [show S = Finset.univ.erase 0 by
          ext x
          simp [S, eq_comm]]
        rw [Finset.card_erase_of_mem (Finset.mem_univ 0)]
        simp
      calc
        (∑ x : X, if x = 0 then 0 else 2 ^ (s - 2)) =
            S.sum (fun _ => 2 ^ (s - 2)) := by
              change (∑ x : X, if x = 0 then 0 else 2 ^ (s - 2)) =
                (Finset.univ.filter (fun x : X => x ≠ 0)).sum
                  (fun _ => 2 ^ (s - 2))
              rw [Finset.sum_filter]
              apply Finset.sum_congr rfl
              intro x hx
              by_cases h : x = 0 <;> simp [h]
        _ = S.card * 2 ^ (s - 2) := by simp
        _ = (Fintype.card X - 1) * 2 ^ (s - 2) := by rw [hS]
    rw [show Fintype.card X = 2 ^ (s - 1) by simp [X, Fintype.card_fun, ZMod.card]] at hsum
    rw [hdecomp]
    rw [show (∑ x : X, Fintype.card {y : X // P x y}) =
        ∑ x : X, (if x = 0 then 0 else 2 ^ (s - 2)) by
          apply Finset.sum_congr rfl
          intro x hx
          exact hfiber x]
    rw [hsum]
    rw [Nat.sub_mul, one_mul, ← pow_add]
    rw [show (s - 1) + (s - 2) = 2 * s - 3 by omega]
  exact ⟨hstruct.1, hstruct.2, hcard⟩
