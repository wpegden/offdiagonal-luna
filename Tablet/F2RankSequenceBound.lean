import Tablet.F2PairDigraph
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Field.ZMod

open scoped BigOperators

set_option maxHeartbeats 2000000

-- [TABLET NODE: F2RankSequenceBound]
theorem F2RankSequenceBound (p k : Nat) (hp : 1 ≤ p) (hk : 1 ≤ k) :
    Fintype.card
        { z : (Fin k → (Fin p → ZMod 2)) × (Fin k → (Fin p → ZMod 2)) //
          ∀ ⦃i j : Fin k⦄, i.val ≤ j.val →
            (∑ r, z.1 i r * z.2 j r) = 1 } ≤
      ∑ t ∈ Finset.Icc 1 p,
        Nat.choose k t * 2 ^ (p * (t + k) - Nat.choose (t + 1) 2) := by
-- BODY
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let B : LinearMap.BilinForm (ZMod 2) (Fin p → ZMod 2) :=
    LinearMap.mk₂ (ZMod 2) (fun x y => ∑ i, x i * y i)
      (by intros; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib])
      (by intros; simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]; rw [Finset.mul_sum])
      (by intros; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
      (by intros; simp only [Pi.smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]; rw [Finset.mul_sum])
  have hBsymm : LinearMap.IsSymm B := by
    constructor
    intro x y
    simp [B, mul_comm]
  have hBnondeg : B.Nondegenerate := by
    constructor
    · intro x hx
      apply (dotProduct_eq_zero_iff.mp ?_)
      intro y
      simpa [B, dotProduct] using hx y
    · intro y hy
      apply (dotProduct_eq_zero_iff.mp ?_)
      intro x
      simpa [B, dotProduct, mul_comm] using hy x
  have hMfinrank : Module.finrank (ZMod 2) (Fin p → ZMod 2) = p := by
    cases p with
    | zero => omega
    | succ p => simp [Module.finrank_fintype_fun_eq_card]
  have hMcard : Fintype.card (Fin p → ZMod 2) = 2 ^ p := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := Fin p → ZMod 2),
      ZMod.card 2, hMfinrank]
  have hspan_card (W : Submodule (ZMod 2) (Fin p → ZMod 2)) :
      Fintype.card W = 2 ^ Module.finrank (ZMod 2) W := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := W), ZMod.card 2]
  have horth_card (W : Submodule (ZMod 2) (Fin p → ZMod 2)) :
      Fintype.card (B.orthogonal W) = 2 ^ (p - Module.finrank (ZMod 2) W) := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := B.orthogonal W),
      ZMod.card 2, B.finrank_orthogonal hBnondeg W,
      hMfinrank]
  have hspan_mem (a : Fin k → (Fin p → ZMod 2)) (i : Fin k) :
      a i ∈ Submodule.span (ZMod 2) (Set.range a) := by
    exact Submodule.subset_span (Set.mem_range_self i)
  have fiber_card {n : Nat} (a : Fin n → (Fin p → ZMod 2))
      (y0 : Fin p → ZMod 2) (hy0 : ∀ i, B (a i) y0 = 1) :
      Fintype.card {y : (Fin p → ZMod 2) // ∀ i, B (a i) y = 1} ≤
        2 ^ (p - Module.finrank (ZMod 2)
          (Submodule.span (ZMod 2) (Set.range a))) := by
    let W : Submodule (ZMod 2) (Fin p → ZMod 2) :=
      Submodule.span (ZMod 2) (Set.range a)
    let f : {y : (Fin p → ZMod 2) // ∀ i, B (a i) y = 1} → B.orthogonal W :=
      fun y => ⟨(y : Fin p → ZMod 2) - y0, by
        rw [LinearMap.BilinForm.mem_orthogonal_iff]
        intro x hx
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
        · intro x hx
          obtain ⟨i, rfl⟩ := hx
          rw [map_sub, y.property i, hy0 i, sub_self]
        · simp
        · intro x z _ _ hx hz
          rw [map_add B]
          simp only [LinearMap.add_apply, hx, hz, add_zero]
        · intro c x _ hx
          rw [map_smul B]
          simp only [LinearMap.smul_apply, hx, smul_zero]⟩
    have hcard := Fintype.card_le_of_injective f (by
      intro y z h
      apply Subtype.ext
      apply sub_left_injective
      exact congrArg Subtype.val h)
    rw [horth_card W] at hcard
    simpa [W] using hcard
  let rankOf (n : Nat) (a : Fin n → (Fin p → ZMod 2)) : Nat :=
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range a))
  have rank_snoc (n : Nat) (a : Fin n → (Fin p → ZMod 2)) (x : Fin p → ZMod 2) :
      rankOf (n + 1) (Fin.snoc a x) =
        if x ∈ Submodule.span (ZMod 2) (Set.range a) then rankOf n a
        else rankOf n a + 1 := by
    have hrange : Set.range (Fin.snoc a x) = insert x (Set.range a) :=
      Fin.range_snoc a x
    by_cases hx : x ∈ Submodule.span (ZMod 2) (Set.range a)
    · unfold rankOf
      rw [Fin.range_snoc, Submodule.span_insert_eq_span hx]
      simp [hx]
    · unfold rankOf
      rw [Fin.range_snoc, Submodule.span_insert]
      rw [sup_comm, Submodule.finrank_sup_span_singleton hx]
      simp [hx]
  let Bad (n : Nat) : Type :=
    {z : (Fin n → (Fin p → ZMod 2)) × (Fin n → (Fin p → ZMod 2)) //
      ∀ ⦃i j : Fin n⦄, i.val ≤ j.val → B (z.1 i) (z.2 j) = 1}
  let At (n r : Nat) : Type := {z : Bad n // rankOf n z.1.1 = r}
  let Fiber (n : Nat) (a : Fin n → (Fin p → ZMod 2)) : Type :=
    {y : (Fin p → ZMod 2) // ∀ i, B (a i) y = 1}
  have fiber_card' {n : Nat} (a : Fin n → (Fin p → ZMod 2)) :
      Fintype.card (Fiber n a) ≤
        2 ^ (p - rankOf n a) := by
    by_cases h : Nonempty (Fiber n a)
    · let y0 : Fin p → ZMod 2 := (Classical.choice h : Fiber n a)
      have hy0 : ∀ i, B (a i) y0 = 1 := (Classical.choice h).property
      simpa [Fiber, rankOf] using fiber_card a y0 hy0
    · letI : IsEmpty (Fiber n a) := not_nonempty_iff.mp h
      simp [Fiber]
  have bad_prefix (n : Nat) (a b : Fin (n + 1) → (Fin p → ZMod 2))
      (h : ∀ ⦃i j : Fin (n + 1)⦄, i.val ≤ j.val → B (a i) (b j) = 1) :
      (∀ ⦃i j : Fin n⦄, i.val ≤ j.val → B (Fin.init a i) (Fin.init b j) = 1) := by
    intro i j hij
    exact h (i := i.castSucc) (j := j.castSucc) (by simpa using hij)
  let pref (n : Nat) (z : Bad (n + 1)) : Bad n :=
    ⟨(Fin.init z.1.1, Fin.init z.1.2), bad_prefix n z.1.1 z.1.2 z.2⟩
  have rank_prefix_cases {n t : Nat} (z : At (n + 1) t) :
      rankOf n (pref n z.1).1.1 = t ∨ rankOf n (pref n z.1).1.1 + 1 = t := by
    have hA : Fin.snoc (Fin.init z.1.1.1) (z.1.1.1 (Fin.last n)) = z.1.1.1 :=
      Fin.snoc_init_self _
    have hz : rankOf (n + 1)
        (Fin.snoc (Fin.init z.1.1.1) (z.1.1.1 (Fin.last n))) = t := by
      rw [hA]
      exact z.2
    rw [rank_snoc] at hz
    split at hz
    · exact Or.inl hz
    · exact Or.inr hz
  let Xspan (n r : Nat) (q : At n r) : Type :=
    {x : (Fin p → ZMod 2) // x ∈ Submodule.span (ZMod 2) (Set.range q.1.1.1)}
  let Xout (n r : Nat) (q : At n r) : Type :=
    {x : (Fin p → ZMod 2) // x ∉ Submodule.span (ZMod 2) (Set.range q.1.1.1)}
  let NonExt (n r : Nat) : Type :=
    Σ q : At n r, Σ x : Xspan n r q, Fiber (n + 1) (Fin.snoc q.1.1.1 x.1)
  let RaiseExt (n r : Nat) : Type :=
    Σ q : At n r, Σ x : Xout n r q, Fiber (n + 1) (Fin.snoc q.1.1.1 x.1)
  have hXspan_card (n r : Nat) (q : At n r) :
      Fintype.card (Xspan n r q) = 2 ^ r := by
    change Fintype.card (Submodule.span (ZMod 2) (Set.range q.1.1.1)) = 2 ^ r
    rw [hspan_card]
    simpa [rankOf] using q.2
  have hXout_card_le (n r : Nat) (q : At n r) :
      Fintype.card (Xout n r q) ≤ 2 ^ p := by
    let f : Xout n r q → (Fin p → ZMod 2) := fun x => x.1
    have hf : Function.Injective f := by
      intro x y h
      exact Subtype.ext h
    have hle := Fintype.card_le_of_injective f hf
    simpa [hMcard] using hle
  let hlast_fiber {n t : Nat} (z : At (n + 1) t) :
      (Fiber (n + 1) (Fin.snoc (Fin.init z.1.1.1)
          (z.1.1.1 (Fin.last n)))) := by
    refine ⟨z.1.1.2 (Fin.last n), ?_⟩
    intro i
    simpa [Fin.snoc_init_self] using
      z.1.2 (i := i) (j := Fin.last n) (by
        have hi : i.val < Nat.succ n := by simpa using i.isLt
        exact Nat.le_of_lt_succ hi)
  have hfiber_span {n r : Nat} (q : At n r) (x : Xspan n r q) :
      Fintype.card (Fiber (n + 1) (Fin.snoc q.1.1.1 x.1)) ≤ 2 ^ (p - r) := by
    have hr : rankOf (n + 1) (Fin.snoc q.1.1.1 x.1) = r := by
      rw [rank_snoc]
      simp [x.2, q.2]
    have h := fiber_card' (Fin.snoc q.1.1.1 x.1)
    simpa [hr] using h
  have hfiber_out {n r : Nat} (q : At n r) (x : Xout n r q) :
      Fintype.card (Fiber (n + 1) (Fin.snoc q.1.1.1 x.1)) ≤
        2 ^ (p - (r + 1)) := by
    have hr : rankOf (n + 1) (Fin.snoc q.1.1.1 x.1) = r + 1 := by
      rw [rank_snoc]
      simp [x.2, q.2]
    have h := fiber_card' (Fin.snoc q.1.1.1 x.1)
    simpa [hr] using h
  have hNonExt_card_le {n r : Nat} (hrp : r ≤ p) :
      Fintype.card (NonExt n r) ≤ Fintype.card (At n r) * 2 ^ p := by
    have hinner (q : At n r) :
        Fintype.card (Σ x : Xspan n r q,
          Fiber (n + 1) (Fin.snoc q.1.1.1 x.1)) ≤ 2 ^ p := by
      rw [Fintype.card_sigma]
      calc
        (∑ x : Xspan n r q,
            Fintype.card (Fiber (n + 1) (Fin.snoc q.1.1.1 x.1))) ≤
            ∑ _x : Xspan n r q, 2 ^ (p - r) := by
              apply Finset.sum_le_sum
              intro x hx
              exact hfiber_span q x
        _ = Fintype.card (Xspan n r q) * 2 ^ (p - r) := by simp
        _ = 2 ^ r * 2 ^ (p - r) := by rw [hXspan_card]
        _ = 2 ^ p := by rw [← pow_add, Nat.add_sub_of_le hrp]
    rw [show Fintype.card (NonExt n r) =
      ∑ q : At n r, Fintype.card (Σ x : Xspan n r q,
        Fiber (n + 1) (Fin.snoc q.1.1.1 x.1)) by
          simp [NonExt, Fintype.card_sigma]]
    calc
      (∑ q : At n r, Fintype.card (Σ x : Xspan n r q,
          Fiber (n + 1) (Fin.snoc q.1.1.1 x.1))) ≤
          ∑ _q : At n r, 2 ^ p := by
            apply Finset.sum_le_sum
            intro q hq
            exact hinner q
      _ = Fintype.card (At n r) * 2 ^ p := by simp
  have hRaiseExt_card_le {n r : Nat} :
      Fintype.card (RaiseExt n r) ≤
        Fintype.card (At n r) * 2 ^ p * 2 ^ (p - (r + 1)) := by
    have hinner (q : At n r) :
        Fintype.card (Σ x : Xout n r q,
          Fiber (n + 1) (Fin.snoc q.1.1.1 x.1)) ≤
          2 ^ p * 2 ^ (p - (r + 1)) := by
      rw [Fintype.card_sigma]
      calc
        (∑ x : Xout n r q,
            Fintype.card (Fiber (n + 1) (Fin.snoc q.1.1.1 x.1))) ≤
            ∑ x : Xout n r q, 2 ^ (p - (r + 1)) := by
              apply Finset.sum_le_sum
              intro x hx
              exact hfiber_out q x
        _ = Fintype.card (Xout n r q) * 2 ^ (p - (r + 1)) := by simp
        _ ≤ 2 ^ p * 2 ^ (p - (r + 1)) := by
          gcongr
          exact hXout_card_le n r q
    rw [show Fintype.card (RaiseExt n r) =
      ∑ q : At n r, Fintype.card (Σ x : Xout n r q,
        Fiber (n + 1) (Fin.snoc q.1.1.1 x.1)) by
          simp [RaiseExt, Fintype.card_sigma]]
    calc
      (∑ q : At n r, Fintype.card (Σ x : Xout n r q,
          Fiber (n + 1) (Fin.snoc q.1.1.1 x.1))) ≤
          ∑ _q : At n r, 2 ^ p * 2 ^ (p - (r + 1)) := by
            apply Finset.sum_le_sum
            intro q hq
            exact hinner q
      _ = Fintype.card (At n r) * 2 ^ p * 2 ^ (p - (r + 1)) := by simp [mul_assoc]
  have hAt_succ_le {n t : Nat} (ht : 1 ≤ t) :
      Fintype.card (At (n + 1) t) ≤
        Fintype.card (NonExt n t) + Fintype.card (RaiseExt n (t - 1)) := by
    let enc : At (n + 1) t → NonExt n t ⊕ RaiseExt n (t - 1) := fun z => by
      have hA : Fin.snoc (Fin.init z.1.1.1) (z.1.1.1 (Fin.last n)) = z.1.1.1 :=
        Fin.snoc_init_self _
      have hprefix : rankOf n (pref n z.1).1.1 =
          rankOf n (Fin.init z.1.1.1) := by rfl
      by_cases hq : rankOf n (pref n z.1).1.1 = t
      · have hx : z.1.1.1 (Fin.last n) ∈
            Submodule.span (ZMod 2) (Set.range (Fin.init z.1.1.1)) := by
          by_contra hx
          have hz := z.2
          rw [← hA, rank_snoc, if_neg hx] at hz
          omega
        let q : At n t := ⟨pref n z.1, hq⟩
        exact Sum.inl ⟨q, ⟨⟨z.1.1.1 (Fin.last n), by simpa [q, pref] using hx⟩,
          by simpa [q, pref] using hlast_fiber z⟩⟩
      · have hqr : rankOf n (pref n z.1).1.1 + 1 = t :=
          (rank_prefix_cases z).resolve_left hq
        have hr : rankOf n (pref n z.1).1.1 = t - 1 := by omega
        have hx : z.1.1.1 (Fin.last n) ∉
            Submodule.span (ZMod 2) (Set.range (Fin.init z.1.1.1)) := by
          intro hx
          have hz := z.2
          rw [← hA, rank_snoc, if_pos hx] at hz
          exact hq (by simpa [hprefix] using hz)
        let q : At n (t - 1) := ⟨pref n z.1, hr⟩
        exact Sum.inr ⟨q, ⟨⟨z.1.1.1 (Fin.last n), by simpa [q, pref] using hx⟩,
          by simpa [q, pref] using hlast_fiber z⟩⟩
    let badExtend (r : Nat) (q : At n r) (x : Fin p → ZMod 2)
        (y : Fiber (n + 1) (Fin.snoc q.1.1.1 x)) : Bad (n + 1) :=
      ⟨(Fin.snoc q.1.1.1 x, Fin.snoc q.1.1.2 y.1), by
        intro i j hij
        revert hij
        revert j
        refine Fin.lastCases ?_ (fun i => ?_) i
        · intro j
          refine Fin.lastCases ?_ (fun j => ?_) j
          · intro hij
            simpa [Fin.snoc_last] using y.2 (Fin.last n)
          · intro hij
            exfalso
            have hj := j.isLt
            have hle : n ≤ j.val := by simpa using hij
            omega
        · intro j
          refine Fin.lastCases ?_ (fun j => ?_) j
          · intro hij
            simpa [Fin.snoc_castSucc, Fin.snoc_last] using y.2 i.castSucc
          · intro hij
            simpa [Fin.snoc_castSucc] using q.1.2 (by simpa using hij)
      ⟩
    let reconstructNon : NonExt n t → At (n + 1) t := fun u =>
      ⟨badExtend t u.1 u.2.1.1 u.2.2,
        by
          dsimp [badExtend]
          rw [rank_snoc]
          simp [u.2.1.2, u.1.2]⟩
    let reconstructRaise : RaiseExt n (t - 1) → At (n + 1) t := fun u =>
      ⟨badExtend (t - 1) u.1 u.2.1.1 u.2.2,
        by
          dsimp [badExtend]
          rw [rank_snoc]
          simp [u.2.1.2, u.1.2]
          omega⟩
    let reconstruct : (NonExt n t ⊕ RaiseExt n (t - 1)) → At (n + 1) t :=
      Sum.elim reconstructNon reconstructRaise
    have hleft (z : At (n + 1) t) : reconstruct (enc z) = z := by
      dsimp [enc, reconstruct, reconstructNon, reconstructRaise]
      split
      · apply Subtype.ext
        apply Subtype.ext
        apply Prod.ext
        · simp [badExtend, pref]
        · have hy : (hlast_fiber z).1 = z.1.1.2 (Fin.last n) := rfl
          simpa [reconstruct, reconstructNon, reconstructRaise, badExtend, pref, hy]
      · apply Subtype.ext
        apply Subtype.ext
        apply Prod.ext
        · simp [badExtend, pref]
        · have hy : (hlast_fiber z).1 = z.1.1.2 (Fin.last n) := rfl
          simpa [reconstruct, reconstructNon, reconstructRaise, badExtend, pref, hy]
    have henc : Function.Injective enc := by
      intro z w hzw
      calc
        z = reconstruct (enc z) := (hleft z).symm
        _ = reconstruct (enc w) := congrArg reconstruct hzw
        _ = w := hleft w
    simpa [Fintype.card_sum] using Fintype.card_le_of_injective enc henc
  have rank_le {n : Nat} (a : Fin n → (Fin p → ZMod 2)) : rankOf n a ≤ n := by
    simpa [Set.finrank, rankOf] using (finrank_range_le_card a)
  have bad_first_ne {n : Nat} (z : Bad (n + 1)) :
      z.1.1 (0 : Fin (n + 1)) ≠ 0 := by
    intro ha
    have hd := z.2 (i := (0 : Fin (n + 1))) (j := (0 : Fin (n + 1))) (by simp)
    have h01 : (0 : ZMod 2) = 1 := by simpa [ha] using hd
    exact zero_ne_one h01
  have rank_pos {n : Nat} (z : Bad (n + 1)) : 1 ≤ rankOf (n + 1) z.1.1 := by
    have hne : Submodule.span (ZMod 2) (Set.range z.1.1) ≠ ⊥ := by
      intro hbot
      have ha : z.1.1 (0 : Fin (n + 1)) = 0 := by
        exact (Submodule.eq_bot_iff _).mp hbot _
          (Submodule.subset_span (Set.mem_range_self (0 : Fin (n + 1))))
      exact bad_first_ne z ha
    have hrne : rankOf (n + 1) z.1.1 ≠ 0 := by
      intro hr
      apply hne
      apply (Submodule.finrank_eq_zero).mp
      simpa [rankOf] using hr
    omega
  have rank_le_p {n : Nat} (a : Fin n → (Fin p → ZMod 2)) : rankOf n a ≤ p := by
    have h := Submodule.finrank_le (Submodule.span (ZMod 2) (Set.range a))
    simpa [rankOf, hMfinrank] using h
  have rank_pos_k (z : Bad k) : 1 ≤ rankOf k z.1.1 := by
    have hne : Submodule.span (ZMod 2) (Set.range z.1.1) ≠ ⊥ := by
      intro hbot
      have ha : z.1.1 (⟨0, by omega⟩ : Fin k) = 0 := by
        exact (Submodule.eq_bot_iff _).mp hbot _
          (Submodule.subset_span (Set.mem_range_self (⟨0, by omega⟩ : Fin k)))
      have hd := z.2 (i := (⟨0, by omega⟩ : Fin k)) (j := (⟨0, by omega⟩ : Fin k)) (by simp)
      have h01 : (0 : ZMod 2) = 1 := by simpa [ha] using hd
      exact zero_ne_one h01
    have hrne : rankOf k z.1.1 ≠ 0 := by
      intro hr
      apply hne
      apply (Submodule.finrank_eq_zero).mp
      simpa [rankOf] using hr
    omega
  have hAt_zero : Fintype.card (At 0 0) = 1 := by
    have hsub : Subsingleton (At 0 0) := by
      constructor
      intro z w
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext <;> funext i <;> exact Fin.elim0 i
    haveI : Nonempty (At 0 0) := by
      refine ⟨⟨⟨(fun i => Fin.elim0 i), (fun i => Fin.elim0 i)⟩, ?_⟩, ?_⟩
      · intro i
        exact Fin.elim0 i
      · simp [rankOf]
    refine Fintype.card_eq_one_iff.mpr ⟨Classical.choice (inferInstance : Nonempty (At 0 0)), ?_⟩
    intro z
    exact Subsingleton.elim z _
  have choose_sq : ∀ u : Nat, Nat.choose (u + 1) 2 ≤ u * u := by
    intro u
    induction u with
    | zero => simp
    | succ u ihu =>
        rw [Nat.choose_succ_succ]
        simp only [Nat.choose_one_right]
        nlinarith [ihu]
  have choose_bound : ∀ u : Nat, Nat.choose (u + 1) 2 ≤ u * (u + 1) := by
    intro u
    induction u with
    | zero => simp
    | succ u ihu =>
        rw [Nat.choose_succ_succ]
        simp only [Nat.choose_one_right]
        nlinarith [ihu]
  have hAt_bound : ∀ n t : Nat, t ≤ p →
      Fintype.card (At n t) ≤
        Nat.choose n t * 2 ^ (p * (t + n) - Nat.choose (t + 1) 2) := by
    intro n
    induction n with
    | zero =>
        intro t htp
        by_cases ht0 : t = 0
        · subst t
          simpa [hAt_zero]
        · have hempty : IsEmpty (At 0 t) := by
            constructor
            intro z
            have hz : rankOf 0 z.1.1.1 = 0 := by simp [rankOf]
            exact ht0 (z.2.symm.trans hz)
          letI : IsEmpty (At 0 t) := hempty
          simp
    | succ n ih =>
        intro t htp
        by_cases ht1 : 1 ≤ t
        · have hrec := hAt_succ_le (n := n) (t := t) ht1
          have hnon := hNonExt_card_le (n := n) (r := t) htp
          have hraise := hRaiseExt_card_le (n := n) (r := t - 1)
          have hih1 := ih t htp
          have hih2 := ih (t - 1) (by omega)
          have hih2' : Fintype.card (At n (t - 1)) ≤
              Nat.choose n (t - 1) *
                2 ^ (p * ((t - 1) + n) - Nat.choose t 2) := by
            simpa [Nat.sub_add_cancel ht1] using hih2
          have hstep : Fintype.card (At (n + 1) t) ≤
              Fintype.card (At n t) * 2 ^ p +
                Fintype.card (At n (t - 1)) * 2 ^ p * 2 ^ (p - t) := by
            calc
              Fintype.card (At (n + 1) t) ≤
                  Fintype.card (NonExt n t) + Fintype.card (RaiseExt n (t - 1)) := hrec
              _ ≤ Fintype.card (At n t) * 2 ^ p +
                    Fintype.card (At n (t - 1)) * 2 ^ p * 2 ^ (p - t) := by
                apply add_le_add hnon
                simpa [Nat.sub_add_cancel ht1] using hraise
          have hexp : p * (t + n + 1) - Nat.choose (t + 1) 2 ≥ 0 := by
            have hc : Nat.choose (t + 1) 2 ≤ p * (t + n + 1) := by
              have hct := choose_bound t
              nlinarith
            omega
          calc
            Fintype.card (At (n + 1) t) ≤
                Fintype.card (At n t) * 2 ^ p +
                  Fintype.card (At n (t - 1)) * 2 ^ p * 2 ^ (p - t) := hstep
            _ ≤ (Nat.choose n t *
                2 ^ (p * (t + n) - Nat.choose (t + 1) 2)) * 2 ^ p +
                  (Nat.choose n (t - 1) *
                2 ^ (p * ((t - 1) + n) - Nat.choose t 2)) * 2 ^ p *
                  2 ^ (p - t) := by
                gcongr
            _ = Nat.choose (n + 1) t *
                2 ^ (p * (t + (n + 1)) - Nat.choose (t + 1) 2) := by
                have hchoose : Nat.choose (t + 1) 2 = Nat.choose t 2 + t := by
                  rw [Nat.choose_succ_succ]
                  simp only [Nat.choose_one_right]
                  simp [Nat.add_comm]
                have hchoose_prev : Nat.choose t 2 ≤ (t - 1) * t := by
                  have h := choose_bound (t - 1)
                  simpa [Nat.sub_add_cancel ht1] using h
                have hA0 : Nat.choose (t + 1) 2 ≤ p * (t + n) := by
                  have h := choose_sq t
                  nlinarith [hp]
                have hB0 : Nat.choose t 2 ≤ p * ((t - 1) + n) := by
                  nlinarith
                have hA :
                    p * (t + n) - Nat.choose (t + 1) 2 + p =
                      p * (t + (n + 1)) - Nat.choose (t + 1) 2 := by
                  rw [← Nat.sub_add_comm hA0]
                  congr 1
                have hXp : p * ((t - 1) + n) + p = p * (t + n) := by
                  have htn : (t - 1) + n + 1 = t + n := by omega
                  calc
                    p * ((t - 1) + n) + p = p * ((t - 1) + n + 1) := by ring
                    _ = p * (t + n) := by rw [htn]
                have hB :
                    (p * ((t - 1) + n) - Nat.choose t 2) + p + (p - t) =
                      p * (t + (n + 1)) - Nat.choose (t + 1) 2 := by
                  calc
                    (p * ((t - 1) + n) - Nat.choose t 2) + p + (p - t) =
                        (p * ((t - 1) + n) + p - Nat.choose t 2) + (p - t) := by
                          rw [← Nat.sub_add_comm hB0]
                    _ = (p * ((t - 1) + n) + p + (p - t)) - Nat.choose t 2 := by
                          exact (Nat.sub_add_comm (le_trans hB0 (Nat.le_add_right _ _))).symm
                    _ = (p * (t + n) + (p - t)) - Nat.choose t 2 := by
                          rw [hXp]
                    _ = (p * (t + n) + p - t) - Nat.choose t 2 := by
                          rw [Nat.add_sub_assoc htp]
                    _ = (p * (t + (n + 1)) - t) - Nat.choose t 2 := by
                          congr 2
                    _ = p * (t + (n + 1)) - (Nat.choose t 2 + t) := by omega
                    _ = p * (t + (n + 1)) - Nat.choose (t + 1) 2 := by rw [hchoose]
                calc
                  (Nat.choose n t *
                      2 ^ (p * (t + n) - Nat.choose (t + 1) 2)) * 2 ^ p +
                      (Nat.choose n (t - 1) *
                      2 ^ (p * ((t - 1) + n) - Nat.choose t 2)) * 2 ^ p * 2 ^ (p - t) =
                      Nat.choose n t *
                          2 ^ (p * (t + n) - Nat.choose (t + 1) 2 + p) +
                        Nat.choose n (t - 1) *
                          2 ^ (p * ((t - 1) + n) - Nat.choose t 2 + p + (p - t)) := by
                            rw [mul_assoc, ← pow_add]
                            rw [mul_assoc, ← pow_add, mul_assoc, ← pow_add]
                            simp only [Nat.add_assoc]
                  _ = (Nat.choose n t + Nat.choose n (t - 1)) *
                        2 ^ (p * (t + (n + 1)) - Nat.choose (t + 1) 2) := by
                            rw [hA, hB]
                            ring
                  _ = Nat.choose (n + 1) t *
                        2 ^ (p * (t + (n + 1)) - Nat.choose (t + 1) 2) := by
                            have hbinom : Nat.choose (n + 1) t =
                                Nat.choose n (t - 1) + Nat.choose n t := by
                              simpa [Nat.sub_add_cancel ht1, Nat.add_comm] using
                                (Nat.choose_succ_succ n (t - 1))
                            rw [hbinom]
                            ring
        · have ht0 : t = 0 := by omega
          subst t
          have hempty : IsEmpty (At (n + 1) 0) := by
            constructor
            intro z
            have hz := rank_pos z.1
            omega
          letI : IsEmpty (At (n + 1) 0) := hempty
          simp
  let I : Finset Nat := Finset.Icc 1 p
  let enc : Bad k → Σ t : {t // t ∈ I}, At k t.1 := fun z => by
    let r := rankOf k z.1.1
    have hr : r ∈ I := by
      change rankOf k z.1.1 ∈ Finset.Icc 1 p
      exact Finset.mem_Icc.mpr ⟨rank_pos_k z, rank_le_p z.1.1⟩
    exact ⟨⟨r, hr⟩, ⟨z, rfl⟩⟩
  let dec : (Σ t : {t // t ∈ I}, At k t.1) → Bad k := fun u => u.2.1
  have hleft (z : Bad k) : dec (enc z) = z := by
    rfl
  have henc : Function.Injective enc := by
    intro z w hzw
    calc
      z = dec (enc z) := (hleft z).symm
      _ = dec (enc w) := congrArg dec hzw
      _ = w := hleft w
  have hcard := Fintype.card_le_of_injective enc henc
  have hcard' : Fintype.card (Bad k) ≤
      ∑ q : {t // t ∈ I}, Fintype.card (At k q.1) := by
    simpa [Fintype.card_sigma] using hcard
  have hsum : (∑ q : {t // t ∈ I}, Fintype.card (At k q.1)) =
      ∑ t ∈ I, Fintype.card (At k t) := by
    simpa [Finset.univ_eq_attach] using
      (Finset.sum_attach I (fun t => Fintype.card (At k t)))
  have hsum_le : (∑ t ∈ I, Fintype.card (At k t)) ≤
      ∑ t ∈ I, Nat.choose k t *
        2 ^ (p * (t + k) - Nat.choose (t + 1) 2) := by
    apply Finset.sum_le_sum
    intro t ht
    have ht' : t ∈ Finset.Icc 1 p := by simpa [I] using ht
    exact hAt_bound k t (Finset.mem_Icc.mp ht').2
  have hfinal : Fintype.card (Bad k) ≤
      ∑ t ∈ I, Nat.choose k t *
        2 ^ (p * (t + k) - Nat.choose (t + 1) 2) := by
    calc
      Fintype.card (Bad k) ≤
          ∑ q : {t // t ∈ I}, Fintype.card (At k q.1) := hcard'
      _ = ∑ t ∈ I, Fintype.card (At k t) := hsum
      _ ≤ ∑ t ∈ I, Nat.choose k t *
          2 ^ (p * (t + k) - Nat.choose (t + 1) 2) := hsum_le
  simpa [Bad, B, LinearMap.mk₂_apply, I] using hfinal
